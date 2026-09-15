#!/usr/bin/env python3
"""Experimental exact CNF intersection using disjoint affine GF(2) components.

This is a research representation, not a general polynomial SAT algorithm.
For t independent OR3 clauses the explicit state list has 3**t components.
No DPLL/CDCL or external solver is called. Gaussian rows use Python bitmasks;
their operation cost grows with bit length and is not a constant-bit-cost model.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable


@dataclass(frozen=True)
class AffineSystem:
    """Canonical consistent reduced equations mask dot x = rhs (mod 2)."""

    nvars: int
    rows: tuple[tuple[int, int], ...] = ()

    def add(self, mask: int, rhs: int) -> AffineSystem | None:
        if mask < 0 or mask.bit_length() > self.nvars or rhs not in (0, 1):
            raise ValueError("invalid GF(2) equation")
        for row, value in self.rows:
            if mask & (1 << (row.bit_length() - 1)):
                mask ^= row
                rhs ^= value
        if mask == 0:
            return self if rhs == 0 else None
        pivot = 1 << (mask.bit_length() - 1)
        rows = [(row ^ mask, value ^ rhs) if row & pivot else (row, value)
                for row, value in self.rows]
        rows.append((mask, rhs))
        rows.sort(key=lambda item: item[0].bit_length(), reverse=True)
        return AffineSystem(self.nvars, tuple(rows))

    def literal(self, literal: int, truth: bool) -> AffineSystem | None:
        if literal == 0 or abs(literal) > self.nvars:
            raise ValueError("literal out of range")
        return self.add(1 << (abs(literal) - 1), int(truth == (literal > 0)))

    def contains(self, point: int) -> bool:
        return 0 <= point < (1 << self.nvars) and all(
            ((mask & point).bit_count() & 1) == rhs for mask, rhs in self.rows)

    def witness(self) -> int:
        """Choose every free variable zero; RREF leaves pivot values explicit."""
        return sum((1 << (mask.bit_length() - 1)) for mask, rhs in self.rows if rhs)

    @property
    def dimension(self) -> int:
        return self.nvars - len(self.rows)

    def project(self, variable: int) -> AffineSystem:
        """Existential projection, keeping the eliminated coordinate free.

        Variables are zero-based here. The returned subset of GF(2)^n is the
        cylinder over the projected relation, so both x values are included.
        """
        if not 0 <= variable < self.nvars:
            raise ValueError("variable out of range")
        bit = 1 << variable
        chosen = next((i for i, (row, _) in enumerate(self.rows) if row & bit), None)
        if chosen is None:
            return self
        pivot_row, pivot_rhs = self.rows[chosen]
        result = AffineSystem(self.nvars)
        for i, (row, rhs) in enumerate(self.rows):
            if i == chosen:
                continue
            if row & bit:
                row ^= pivot_row
                rhs ^= pivot_rhs
            updated = result.add(row, rhs)
            assert updated is not None
            result = updated
        return result


@dataclass
class UnionResult:
    status: str
    components: list[AffineSystem]
    component_counts: list[int]
    gaussian_updates: int
    witness: int | None
    reason: str = ""


def intersect_cnf(nvars: int, clauses: Iterable[Iterable[int]], *,
                  equations: Iterable[tuple[int, int]] = (),
                  max_components: int = 100_000) -> UnionResult:
    """Exact disjoint union of all models on completion; UNKNOWN on a cap.

    Initial affine equations are supplied explicitly. This prototype does not
    infer hidden XOR gates from arbitrary clause encodings. Clauses are split
    into disjoint cases according to their first true literal.
    """
    if nvars < 0 or max_components < 1:
        raise ValueError("invalid size or component limit")
    state = AffineSystem(nvars)
    updates = 0
    for mask, rhs in equations:
        updates += 1
        candidate = state.add(mask, rhs)
        if candidate is None:
            return UnionResult("UNSAT", [], [0], updates, None)
        state = candidate
    components = [state]
    counts = [1]
    for original in clauses:
        clause = tuple(dict.fromkeys(original))
        if any(lit == 0 or abs(lit) > nvars for lit in clause):
            raise ValueError("literal out of range")
        if any(-lit in clause for lit in clause):
            counts.append(len(components))
            continue
        next_components = []
        for component in components:
            remaining = component
            for literal in clause:
                updates += 1
                satisfied = remaining.literal(literal, True)
                if satisfied is not None:
                    if len(next_components) == max_components:
                        return UnionResult("UNKNOWN", [], counts, updates, None,
                                           "explicit affine component cap exceeded")
                    next_components.append(satisfied)
                updates += 1
                remaining = remaining.literal(literal, False)
                if remaining is None:
                    break
        components = next_components
        counts.append(len(components))
        if not components:
            return UnionResult("UNSAT", [], counts, updates, None)
    return UnionResult("SAT", components, counts, updates, components[0].witness())
