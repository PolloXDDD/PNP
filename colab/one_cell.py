#!/usr/bin/env python3
"""Exact Boolean bucket elimination. General worst-case cost is exponential.

Core: exists x (H & G(x)) = H & (G(0) | G(1)), if H is independent of x.
Dense tables preserve correlations; reverse choices reconstruct a checked model.
No external solver, randomness, DPLL or unproved polynomial oracle is used.
"""
from __future__ import annotations
import argparse
import json
import math
import time
from dataclasses import dataclass, field
from pathlib import Path


class DimacsError(ValueError):
    pass


class ResourceLimit(RuntimeError):
    pass


def _integer(token: str) -> int:
    digits = token[1:] if token[:1] in ('+', '-') else token
    if not digits or any(c < '0' or c > '9' for c in digits):
        raise ValueError('expected an ASCII decimal integer')
    return int(token)


@dataclass
class CNF:
    nvars: int
    clauses: list[tuple[int, ...]]


def parse_dimacs(text: str, max_vars: int = 1_000_000) -> CNF:
    """Strict DIMACS with multiline clauses, c comments and optional % end."""
    text = text.removeprefix('\ufeff')
    nvars = declared = None
    clauses, pending = [], []
    for lineno, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('%'):
            break
        parts = line.split()
        if parts[0] == 'p':
            if nvars is not None or clauses or pending or len(parts) != 4 or parts[1] != 'cnf':
                raise DimacsError(f'line {lineno}: invalid or repeated p cnf header')
            try:
                nvars, declared = _integer(parts[2]), _integer(parts[3])
            except ValueError as exc:
                raise DimacsError(f'line {lineno}: noninteger header') from exc
            if nvars < 0 or declared < 0:
                raise DimacsError('negative header count')
            if nvars > max_vars:
                raise ResourceLimit(f'declared variables {nvars} exceed limit {max_vars}')
            continue
        if nvars is None:
            raise DimacsError(f'line {lineno}: missing p cnf header')
        for token in parts:
            try:
                lit = _integer(token)
            except ValueError as exc:
                raise DimacsError(f'line {lineno}: invalid literal {token!r}') from exc
            if abs(lit) > nvars:
                raise DimacsError(f'line {lineno}: literal outside declared range')
            if lit == 0:
                clauses.append(tuple(pending))
                pending = []
                if len(clauses) > declared:
                    raise DimacsError('more clauses than declared')
            else:
                pending.append(lit)
    if nvars is None:
        raise DimacsError('missing p cnf header')
    if pending:
        raise DimacsError('unterminated final clause; expected 0')
    if len(clauses) != declared:
        raise DimacsError(f'expected {declared} clauses, found {len(clauses)}')
    return CNF(nvars, clauses)


@dataclass
class Factor:
    scope: tuple[int, ...]
    table: bytearray


@dataclass
class Result:
    status: str
    model: list[bool] | None = None
    reason: str = ''
    stats: dict = field(default_factory=dict)


def verify_model(cnf: CNF, model: list[bool]) -> bool:
    return len(model) == cnf.nvars + 1 and all(
        any(model[abs(lit)] == (lit > 0) for lit in clause)
        for clause in cnf.clauses)


def solve(cnf: CNF, *, max_width: int = 22, max_cells: int = 50_000_000,
          timeout: float = 60.0, order: str = 'ascending') -> Result:
    """Return SAT/UNSAT if completed, UNKNOWN on limits.

    width counts every variable in the joined scope, including x. `cells`
    counts cumulative byte-table cells allocated, including witness tables.
    Time budget covers solving, not file parsing or writing. UNKNOWN carries no
    satisfiability conclusion. Limits never change SAT into UNSAT.
    """
    if max_width < 0 or max_cells < 0 or not math.isfinite(timeout) or timeout < 0:
        raise ValueError('resource limits must be finite and nonnegative')
    if order not in ('ascending', 'min-degree'):
        raise ValueError('unknown variable order')
    start = time.monotonic()
    stats = dict(nvars=cnf.nvars, clauses=len(cnf.clauses), order=order,
                 max_width=0, cells=0, rows=0, eliminated=0)

    def finish(status, model=None, reason=''):
        stats['elapsed_seconds'] = time.monotonic() - start
        return Result(status, model, reason, stats.copy())

    def check_time():
        if time.monotonic() - start >= timeout:
            raise ResourceLimit('time budget exceeded')

    def reserve(width, copies=1):
        check_time()
        stats['max_width'] = max(stats['max_width'], width)
        if width > max_width:
            raise ResourceLimit(f'scope width {width} exceeds limit {max_width}')
        # Check bit length before shifting to avoid constructing huge integers.
        remaining = max_cells - stats['cells']
        if remaining < copies or width >= (remaining // copies).bit_length():
            raise ResourceLimit('cumulative table cell budget exceeded')
        count = 1 << width
        stats['cells'] += copies * count
        return count

    factors: dict[int, Factor] = {}
    buckets: dict[int, set[int]] = {}
    serial = 0

    def add(factor):
        nonlocal serial
        i, serial = serial, serial + 1
        factors[i] = factor
        for v in factor.scope:
            buckets.setdefault(v, set()).add(i)

    try:
        # Empty clauses are contradictions independently of any table budget.
        if any(not c for c in cnf.clauses):
            return finish('UNSAT')
        for clause in cnf.clauses:
            check_time()
            literals = set(clause)
            if any(-lit in literals for lit in literals):
                continue
            scope = tuple(sorted(abs(lit) for lit in literals))
            size = reserve(len(scope))
            table = bytearray(b'\x01') * size
            negative = {abs(lit) for lit in literals if lit < 0}
            forbidden = sum(1 << j for j, v in enumerate(scope) if v in negative)
            table[forbidden] = 0
            add(Factor(scope, table))
        records = []
        ascending = sorted(buckets)
        while buckets:
            check_time()
            if order == 'ascending':
                v = ascending[stats['eliminated']]
            else:
                def score(x):
                    neighbors = set()
                    for i in buckets[x]:
                        neighbors.update(factors[i].scope)
                    return len(neighbors), x
                v = min(buckets, key=score)
            ids = sorted(buckets[v])
            selected = [factors[i] for i in ids]
            union = sorted({x for f in selected for x in f.scope})
            width = len(union)
            stats['max_width'] = max(stats['max_width'], width)
            if width > max_width:
                raise ResourceLimit(f'scope width {width} exceeds limit {max_width}')
            rest = tuple(x for x in union if x != v)
            size = reserve(len(rest), 2)
            projected, choices = bytearray(size), bytearray(size)
            positions = {x: j for j, x in enumerate(rest)}
            plans = []
            for f in selected:
                mapping = [(positions[x], j) for j, x in enumerate(f.scope) if x != v]
                pivot = 1 << f.scope.index(v)
                plans.append((f.table, mapping, pivot))
            any_true = False
            for row in range(size):
                if row % 1024 == 0:
                    check_time()
                ok0, ok1 = True, True
                for table, mapping, pivot in plans:
                    index = 0
                    for src, dst in mapping:
                        index |= ((row >> src) & 1) << dst
                    ok0 = ok0 and bool(table[index])
                    ok1 = ok1 and bool(table[index | pivot])
                    if not ok0 and not ok1:
                        break
                if ok0 or ok1:
                    projected[row] = 1
                    choices[row] = 0 if ok0 else 1
                    any_true = True
            stats['rows'] += size
            if not any_true:
                return finish('UNSAT')
            records.append((v, rest, choices))
            for i in ids:
                f = factors.pop(i)
                for x in f.scope:
                    buckets[x].remove(i)
            del buckets[v]
            # Retain even constant-true scopes to make width accounting explicit.
            if rest:
                add(Factor(rest, projected))
            stats['eliminated'] += 1
        model = [False] * (cnf.nvars + 1)
        for v, rest, choices in reversed(records):
            check_time()
            row = sum(int(model[x]) << j for j, x in enumerate(rest))
            model[v] = bool(choices[row])
        check_time()
        if not verify_model(cnf, model):
            raise AssertionError('internal error: reconstructed model failed validation')
        return finish('SAT', model)
    except (ResourceLimit, MemoryError) as exc:
        return finish('UNKNOWN', reason=str(exc) or 'memory allocation failed')


def result_text(result: Result) -> str:
    labels = {'SAT': 'SATISFIABLE', 'UNSAT': 'UNSATISFIABLE', 'UNKNOWN': 'UNKNOWN'}
    lines = ['c Exact Boolean bucket elimination; general cost is exponential',
             's ' + labels[result.status]]
    if result.reason:
        lines.append('c reason ' + result.reason.replace('\n', ' '))
    if result.model is not None:
        literals = [str(i if result.model[i] else -i) for i in range(1, len(result.model))]
        for j in range(0, len(literals), 20):
            lines.append('v ' + ' '.join(literals[j:j+20]) + (' 0' if j + 20 >= len(literals) else ''))
        if not literals:
            lines.append('v 0')
    lines.append('c stats ' + json.dumps(result.stats, sort_keys=True))
    return '\n'.join(lines) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, default=Path('solution.txt'))
    parser.add_argument('--max-width', type=int, default=22)
    parser.add_argument('--max-cells', type=int, default=50_000_000)
    parser.add_argument('--max-vars', type=int, default=1_000_000)
    parser.add_argument('--timeout', type=float, default=60.0)
    parser.add_argument('--order', choices=('ascending', 'min-degree'), default='ascending')
    args = parser.parse_args(argv)
    try:
        cnf = parse_dimacs(args.input.read_text(encoding='utf-8-sig'), args.max_vars)
        result = solve(cnf, max_width=args.max_width, max_cells=args.max_cells,
                       timeout=args.timeout, order=args.order)
    except ResourceLimit as exc:
        result = Result('UNKNOWN', reason=str(exc))
    except (ValueError, OSError) as exc:
        print(f'ERROR: {exc}')
        return 2
    try:
        output = result_text(result)
        args.output.write_text(output, encoding='utf-8')
        print(output, end='')
    except OSError as exc:
        print(f'ERROR writing result: {exc}')
        return 2
    return {'SAT': 10, 'UNSAT': 20, 'UNKNOWN': 0}[result.status]



# Upload one or several DIMACS .cnf files; download each corresponding .txt.
from google.colab import files
MAX_WIDTH = 22
MAX_CELLS = 50_000_000
TIMEOUT_SECONDS = 60.0
ORDER = 'ascending'
uploaded = files.upload()
for uploaded_name, data in uploaded.items():
    try:
        instance = parse_dimacs(data.decode('utf-8-sig'))
        answer = solve(instance, max_width=MAX_WIDTH, max_cells=MAX_CELLS,
                       timeout=TIMEOUT_SECONDS, order=ORDER)
        report = result_text(answer)
    except ResourceLimit as exc:
        report = result_text(Result('UNKNOWN', reason=str(exc)))
    except (ValueError, UnicodeError) as exc:
        report = 's ERROR\nc ' + str(exc).replace('\n', ' ') + '\n'
    output_name = Path(uploaded_name).name + '.solution.txt'
    Path(output_name).write_text(report, encoding='utf-8')
    print(uploaded_name, report.splitlines()[:3])
    files.download(output_name)
