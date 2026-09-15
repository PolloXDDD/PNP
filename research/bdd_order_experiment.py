#!/usr/bin/env python3
"""Small independent reduced ordered BDD implementation for ordering audits.

There is no claim of polynomial worst-case BDD size. Global interned node
counts include transient nodes; reachable counts describe a particular factor.
"""
from __future__ import annotations

from functools import lru_cache


class NodeLimit(RuntimeError):
    pass


class BDD:
    def __init__(self, order: list[int], max_nodes: int = 1_000_000):
        if len(order) != len(set(order)):
            raise ValueError("BDD order repeats variables")
        self.order = order
        self.rank = {variable: i for i, variable in enumerate(order)}
        self.nodes: list[tuple[int, int, int] | None] = [None, None]
        self.unique: dict[tuple[int, int, int], int] = {}
        self.max_nodes = max_nodes
        self.operations = 0

    def make(self, variable: int, low: int, high: int) -> int:
        if low == high:
            return low
        key = (variable, low, high)
        if key in self.unique:
            return self.unique[key]
        if len(self.nodes) >= self.max_nodes:
            raise NodeLimit("BDD interned-node cap exceeded")
        identifier = len(self.nodes)
        self.nodes.append(key)
        self.unique[key] = identifier
        return identifier

    def literal(self, literal: int) -> int:
        variable = abs(literal)
        if variable not in self.rank or literal == 0:
            raise ValueError("invalid literal")
        return self.make(variable, int(literal < 0), int(literal > 0))

    @lru_cache(maxsize=None)
    def apply(self, operation: str, left: int, right: int) -> int:
        self.operations += 1
        if operation not in ("and", "or"):
            raise ValueError("unsupported operation")
        if left <= 1 and right <= 1:
            return int((bool(left) and bool(right)) if operation == "and"
                       else (bool(left) or bool(right)))
        if left == right:
            return left
        if operation == "and":
            if left == 0 or right == 0:
                return 0
            if left == 1:
                return right
            if right == 1:
                return left
        if operation == "or":
            if left == 1 or right == 1:
                return 1
            if left == 0:
                return right
            if right == 0:
                return left
        if left > right:
            return self.apply(operation, right, left)
        left_node, right_node = self.nodes[left], self.nodes[right]
        assert left_node is not None and right_node is not None
        variable = min((left_node[0], right_node[0]), key=self.rank.__getitem__)
        lo_left, hi_left = left_node[1:] if left_node[0] == variable else (left, left)
        lo_right, hi_right = right_node[1:] if right_node[0] == variable else (right, right)
        return self.make(variable, self.apply(operation, lo_left, lo_right),
                         self.apply(operation, hi_left, hi_right))

    @lru_cache(maxsize=None)
    def restrict(self, node: int, variable: int, value: bool) -> int:
        if node <= 1:
            return node
        entry = self.nodes[node]
        assert entry is not None
        current, low, high = entry
        if current == variable:
            return high if value else low
        if self.rank[current] > self.rank[variable]:
            return node
        return self.make(current, self.restrict(low, variable, value),
                         self.restrict(high, variable, value))

    def project(self, node: int, variable: int) -> int:
        return self.apply("or", self.restrict(node, variable, False),
                          self.restrict(node, variable, True))

    def evaluate(self, node: int, point: int) -> bool:
        while node > 1:
            entry = self.nodes[node]
            assert entry is not None
            variable, low, high = entry
            node = high if point & (1 << (variable - 1)) else low
        return bool(node)

    def support(self, node: int) -> set[int]:
        todo, seen, variables = [node], set(), set()
        while todo:
            current = todo.pop()
            if current <= 1 or current in seen:
                continue
            seen.add(current)
            variable, low, high = self.nodes[current]  # type: ignore[misc]
            variables.add(variable)
            todo.extend((low, high))
        return variables

    def reachable_count(self, node: int) -> int:
        """Count reachable decision nodes, excluding terminal constants."""
        todo, seen = [node], set()
        while todo:
            current = todo.pop()
            if current <= 1 or current in seen:
                continue
            seen.add(current)
            _, low, high = self.nodes[current]  # type: ignore[misc]
            todo.extend((low, high))
        return len(seen)

    def clause(self, literals: tuple[int, ...] | list[int]) -> int:
        node = 0
        for literal in literals:
            node = self.apply("or", node, self.literal(literal))
        return node


def bucket_decide(clauses: list[tuple[int, ...]], bdd_order: list[int],
                  elimination_order: list[int], *, max_nodes: int = 1_000_000) -> dict:
    """Exact small research decision experiment; no executable witness contract."""
    if set(bdd_order) != set(elimination_order) or len(elimination_order) != len(set(elimination_order)):
        raise ValueError("orders must be permutations of the same variables")
    bdd = BDD(bdd_order, max_nodes)
    factors: list[tuple[set[int], int]] = []
    max_factor = 0
    steps = []
    status = "SAT"
    try:
        for clause in clauses:
            node = bdd.clause(clause)
            max_factor = max(max_factor, bdd.reachable_count(node))
            if node == 0:
                status = "UNSAT"
                break
            if node != 1:
                factors.append((bdd.support(node), node))
        if status == "SAT":
            for variable in elimination_order:
                selected = [(scope, node) for scope, node in factors if variable in scope]
                factors = [(scope, node) for scope, node in factors if variable not in scope]
                joined = 1
                for _, node in selected:
                    joined = bdd.apply("and", joined, node)
                    max_factor = max(max_factor, bdd.reachable_count(joined))
                    if joined == 0:
                        break
                projected = bdd.project(joined, variable)
                max_factor = max(max_factor, bdd.reachable_count(projected))
                steps.append({"variable": variable, "bucket_factors": len(selected),
                              "joined_nodes": bdd.reachable_count(joined),
                              "projected_nodes": bdd.reachable_count(projected)})
                if projected == 0:
                    status = "UNSAT"
                    break
                if projected != 1:
                    factors.append((bdd.support(projected), projected))
        if status == "SAT":
            assert not factors
    except (NodeLimit, RecursionError, MemoryError):
        status = "UNKNOWN"
    return {"status": status, "max_reachable_factor_nodes": max_factor,
            "interned_nodes_including_terminals": len(bdd.nodes),
            "uncached_apply_calls": bdd.operations, "steps": steps}


def pigeonhole(holes: int) -> tuple[list[tuple[int, ...]], list[int], list[int]]:
    """Standard PHP with holes rows and holes+1 pigeons columns (Mengel 2023)."""
    pigeons = holes + 1
    variable = lambda row, col: row * pigeons + col + 1
    clauses = [tuple(variable(row, col) for row in range(holes))
               for col in range(pigeons)]
    clauses += [(-variable(row, first), -variable(row, second))
                for row in range(holes) for first in range(pigeons)
                for second in range(first + 1, pigeons)]
    rows = [variable(row, col) for row in range(holes) for col in range(pigeons)]
    columns = [variable(row, col) for col in range(pigeons) for row in range(holes)]
    return clauses, rows, columns
