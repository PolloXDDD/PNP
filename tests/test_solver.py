"""Independent oracle, cross-language and I/O tests (Python standard library).

Run: python -m unittest discover -s tests -v
The oracle enumerates assignments directly from raw clauses and does not reuse
factor operations, normalization, elimination or witness reconstruction.
"""
from __future__ import annotations
import contextlib
import importlib.util
import io
import itertools
import json
from pathlib import Path
import random
import runpy
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
import sat_eliminate as solver


def brute_force(n, clauses):
    for bits in itertools.product((False, True), repeat=n):
        if all(any(bits[abs(x) - 1] == (x > 0) for x in clause) for clause in clauses):
            return [False, *bits]
    return None


def dimacs(n, clauses):
    return f'p cnf {n} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + (' ' if c else '') + '0\n' for c in clauses)


def read_result(text):
    status = model = None
    stats = {}
    assigned = {}
    for line in text.splitlines():
        if line.startswith('s '):
            status = {'SATISFIABLE': 'SAT', 'UNSATISFIABLE': 'UNSAT', 'UNKNOWN': 'UNKNOWN'}[line[2:]]
        if line.startswith('v '):
            for raw in line[2:].split():
                literal = int(raw)
                if literal:
                    if abs(literal) in assigned:
                        raise AssertionError('repeated variable in result model')
                    assigned[abs(literal)] = literal > 0
        if line.startswith('c stats '):
            stats = json.loads(line[len('c stats '):])
    if status == 'SAT':
        model = [False] + [assigned[i] for i in range(1, len(assigned) + 1)]
    return status, model, stats


class SolverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='pnp-tests-')
        cls.folder = Path(cls.tmp.name)
        cls.exe = cls.folder / 'sat_eliminate'
        build = subprocess.run(['g++', '-std=c++17', '-O3', '-Wall', '-Wextra', '-Wpedantic',
                                str(ROOT / 'src/sat_eliminate.cpp'), '-o', str(cls.exe)],
                               capture_output=True, text=True, timeout=60)
        if build.returncode or build.stderr:
            raise AssertionError(f'C++ compilation must be warning-free: {build.stdout}\n{build.stderr}')
        cls.input = cls.folder / 'input.cnf'
        cls.output = cls.folder / 'solution.txt'

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def cpp(self, text, *flags):
        self.input.write_text(text, encoding='utf-8')
        return subprocess.run([str(self.exe), str(self.input), *map(str, flags)],
                              capture_output=True, text=True, timeout=15)

    def compare(self, n, clauses, order):
        expected_model = brute_force(n, clauses)
        expected = 'SAT' if expected_model is not None else 'UNSAT'
        cnf = solver.CNF(n, [tuple(c) for c in clauses])
        result = solver.solve(cnf, order=order, timeout=10, max_width=16)
        self.assertEqual(result.status, expected)
        c = self.cpp(dimacs(n, clauses), '--order', order, '--timeout', 10, '--max-width', 16)
        self.assertEqual(c.returncode, 10 if expected == 'SAT' else 20, c.stderr)
        status, model, stats = read_result(c.stdout)
        self.assertEqual(status, expected)
        for key in ('nvars', 'clauses', 'order', 'max_width', 'cells', 'rows', 'eliminated'):
            self.assertEqual(stats[key], result.stats[key], (key, clauses, order, c.stdout, result.stats))
        if status == 'SAT':
            self.assertEqual(len(model), n + 1)
            # Verify raw clauses without using the solver's own validator.
            self.assertTrue(all(any(model[abs(x)] == (x > 0) for x in clause) for clause in clauses))
            self.assertTrue(all(any(result.model[abs(x)] == (x > 0) for x in clause) for clause in clauses))
            self.assertEqual(model, result.model)  # deterministic false-first choices
        self.assertGreaterEqual(stats['elapsed_seconds'], 0)

    def test_all_512_two_variable_formulas_each_order(self):
        clauses = [tuple((i + 1) * sign for i, sign in enumerate(signs) if sign)
                   for signs in itertools.product((-1, 0, 1), repeat=2)]
        self.assertEqual(len(clauses), 9)
        for mask in range(1 << len(clauses)):
            formula = [c for i, c in enumerate(clauses) if (mask >> i) & 1]
            for order in ('ascending', 'min-degree'):
                with self.subTest(mask=mask, order=order):
                    self.compare(2, formula, order)

    def test_seeded_random_up_to_ten_variables(self):
        rng = random.Random(20260915)
        for case in range(160):
            n = 1 + case % 10
            clauses = []
            for _ in range(rng.randrange(0, 5 * n + 1)):
                # Mix ordinary clauses with repeated variables and tautologies.
                k = rng.randrange(1, min(n, 5) + 1)
                variables = rng.sample(range(1, n + 1), k)
                clause = [v if rng.getrandbits(1) else -v for v in variables]
                if clause and rng.randrange(7) == 0:
                    clause.append(rng.choice(clause))
                if clause and rng.randrange(13) == 0:
                    clause.append(-clause[0])
                clauses.append(clause)
            for order in ('ascending', 'min-degree'):
                with self.subTest(case=case, order=order):
                    self.compare(n, clauses, order)

    def test_valid_dimacs_and_percent_terminator(self):
        cases = [
            ('p cnf 0 0\n', 'SAT'),
            ('p cnf 0 1\n0\n', 'UNSAT'),
            ('\ufeffc UTF8 BOM\r\np cnf 3 2\r\n1\r\n c between clause fragments\r\n-2 0 3 0\r\n', 'SAT'),
            ('p cnf 1 1\n+1 +0\n%\n0\nignored trailer\n', 'SAT'),
            ('p cnf 1 2\n1 1 -1 0\n-1 0\n', 'SAT'),
            ('p cnf 4 0\n% anything after percent is ignored\n', 'SAT'),
        ]
        for text, expected in cases:
            with self.subTest(text=text):
                cnf = solver.parse_dimacs(text)
                self.assertEqual(solver.solve(cnf).status, expected)
                process = self.cpp(text)
                self.assertEqual(process.returncode, 10 if expected == 'SAT' else 20, process.stderr)
                self.assertEqual(read_result(process.stdout)[0], expected)

    def test_malformed_dimacs_is_error_never_unsat(self):
        bad = ['', '1 0\n', '%\n', 'p cnf 1 1\n1\n', 'p cnf 1 2\n1 0\n',
               'p cnf 1 0\n0\n', 'p cnf 1 1\n2 0\n', 'p cnf 1 0\np cnf 1 0\n',
               'p cnf 1 1\n1.0 0\n', 'p cnf 1 1\n1_0 0\n', 'p cnf 1 1\n１ 0\n',
               'p cnf 1 1\n+ 0\n', 'p cnf -1 0\n', 'p cnf 1 1 extra\n',
               'p cnf 1 1\n1\n%\n0\n', 'p cnf 1 1\n%\n1 0\n',
               'p cnf １ 0\n', 'p cnf 1_0 0\n', 'p cnf 1 0\n1 0 c trailing\n']
        for text in bad:
            with self.subTest(text=text):
                with self.assertRaises(solver.DimacsError):
                    solver.parse_dimacs(text)
                p = self.cpp(text)
                self.assertEqual(p.returncode, 2, (text, p.stdout, p.stderr))
                self.assertNotIn('s UNSATISFIABLE', p.stdout)

    def test_limits_never_claim_unsat(self):
        text = 'p cnf 3 2\n1 2 0\n-1 3 0\n'
        cnf = solver.parse_dimacs(text)
        for kwargs, flags in [({'timeout': 0}, ['--timeout', 0]),
                              ({'max_width': 1}, ['--max-width', 1]),
                              ({'max_cells': 0}, ['--max-cells', 0]),
                              ({'max_cells': 8}, ['--max-cells', 8])]:
            with self.subTest(kwargs=kwargs):
                result = solver.solve(cnf, **kwargs)
                self.assertEqual(result.status, 'UNKNOWN')
                p = self.cpp(text, *flags)
                self.assertEqual(p.returncode, 0, p.stderr)
                status, model, stats = read_result(p.stdout)
                self.assertEqual(status, 'UNKNOWN')
                self.assertIsNone(model)
                self.assertEqual(stats['cells'], result.stats['cells'])
        with self.assertRaises(solver.ResourceLimit):
            solver.parse_dimacs(text, max_vars=2)
        self.assertEqual(self.cpp(text, '--max-vars', 2).returncode, 0)
        # Immediate empty-clause proof does not consume a search/table budget.
        empty = 'p cnf 0 1\n0\n'
        self.assertEqual(solver.solve(solver.parse_dimacs(empty), timeout=0, max_cells=0).status, 'UNSAT')
        self.assertEqual(self.cpp(empty, '--timeout', 0, '--max-cells', 0).returncode, 20)

    def test_join_width_includes_pivot_and_counts_witness_bytes(self):
        # Both input scopes have width 2; joining at variable 1 produces width 3.
        cnf = solver.parse_dimacs('p cnf 3 2\n1 2 0\n-1 3 0\n')
        r = solver.solve(cnf, max_width=2)
        self.assertEqual((r.status, r.stats['max_width'], r.stats['cells']), ('UNKNOWN', 3, 8))
        done = solver.solve(cnf)
        self.assertEqual(done.stats['cells'], 8 + 8 + 4 + 2)
        self.assertEqual(done.stats['rows'], 4 + 2 + 1)
        self.assertEqual(done.stats['eliminated'], 3)

    def test_cli_output_and_errors(self):
        self.input.write_text('p cnf 3 1\n1 0\n')
        for command in ([sys.executable, str(ROOT / 'src/sat_eliminate.py')], [str(self.exe)]):
            p = subprocess.run([*command, str(self.input), '--output', str(self.output)],
                               capture_output=True, text=True, timeout=15)
            self.assertEqual(p.returncode, 10, p.stderr)
            status, model, stats = read_result(self.output.read_text())
            self.assertEqual(status, 'SAT')
            self.assertEqual(len(model), 4)
            for flags in (['--timeout', '-1'], ['--timeout', 'nan'], ['--timeout', 'inf'], ['--max-cells', '-1']):
                q = subprocess.run([*command, str(self.input), *flags], capture_output=True, text=True, timeout=15)
                self.assertEqual(q.returncode, 2, (command, flags, q.stdout, q.stderr))

    def test_single_cell_colab_upload_and_download(self):
        cell = ROOT / 'colab/one_cell.py'
        payload = b'c Upload smoke test\np cnf 3 2\n1 2 0\n-1 3 0\n'
        downloaded = []
        files = types.SimpleNamespace(upload=lambda: {'input.cnf': payload},
                                      download=lambda path: downloaded.append((str(path), Path(path).read_text())))
        google = types.ModuleType('google')
        colab = types.ModuleType('google.colab')
        colab.files = files
        google.colab = colab
        # Use a subprocess-free execution of the exact generated cell, including
        # embedded solver source, with only Colab's browser I/O mocked.
        with tempfile.TemporaryDirectory(prefix='pnp-colab-') as temp:
            import os
            old = os.getcwd()
            try:
                os.chdir(temp)
                with patch.dict(sys.modules, {'google': google, 'google.colab': colab}):
                    with contextlib.redirect_stdout(io.StringIO()):
                        runpy.run_path(str(cell), run_name='__colab_cell__')
            finally:
                os.chdir(old)
        self.assertEqual(len(downloaded), 1)
        self.assertTrue(downloaded[0][0].endswith('.txt'))
        status, model, stats = read_result(downloaded[0][1])
        self.assertEqual(status, 'SAT')
        self.assertTrue(any(model[abs(x)] == (x > 0) for x in (1, 2)))
        self.assertTrue(any(model[abs(x)] == (x > 0) for x in (-1, 3)))
        notebook = json.loads((ROOT / 'colab/PNP_exact_elimination.ipynb').read_text())
        code_cells = [c for c in notebook['cells'] if c['cell_type'] == 'code']
        self.assertEqual(len(code_cells), 1)
        self.assertEqual(''.join(code_cells[0]['source']), cell.read_text())


if __name__ == '__main__':
    unittest.main()
