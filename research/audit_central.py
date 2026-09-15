#!/usr/bin/env python3
"""Independent finite audits for research/central_argument.md.

Uses exhaustive semantics for small instances; does not import the production
solver. Every assertion is active under ordinary Python invocation. Finite
experiments do not prove general complexity bounds or P=NP.
"""
from __future__ import annotations

import itertools
import json
import platform
import random
import time
from pathlib import Path

from affine_union import AffineSystem, intersect_cnf
from bdd_order_experiment import BDD, bucket_decide, pigeonhole


def satisfies(clauses, point):
    return all(any(bool(point & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in clause) for clause in clauses)


def audit_local_identity():
    comparisons = 0
    recovery_models = 0
    for g in range(1 << 8):
        for h in range(1 << 4):
            for rest in range(4):
                g0, g1 = bool(g & (1 << (2 * rest))), bool(g & (1 << (2 * rest + 1)))
                independent = bool(h & (1 << rest))
                left = any(independent and branch for branch in (g0, g1))
                right = independent and (g0 or g1)
                assert left == right
                if g0 or g1:
                    witness = 0 if g0 else 1
                    assert (g0, g1)[witness]
                comparisons += 1
        table = [bool(g & (1 << row)) for row in range(8)]
        records = []
        for _ in range(3):
            choices = [0 if table[row] else 1 for row in range(0, len(table), 2)]
            table = [table[row] or table[row + 1] for row in range(0, len(table), 2)]
            records.append(choices)
        if table[0]:
            point = 0
            for choices in reversed(records):
                point = 2 * point + choices[point]
            assert bool(g & (1 << point))
            recovery_models += 1
        else:
            assert g == 0
    return {"bucket_identity_comparisons": comparisons,
            "all_three_variable_functions": 256,
            "reconstructed_models": recovery_models}


def xor_gate(left, right, output):
    # Exclude precisely the assignments violating output = left XOR right.
    clauses = []
    for a, b, c in itertools.product((0, 1), repeat=3):
        if c != (a ^ b):
            clauses.append(tuple(-v if bit else v for v, bit in
                                 ((left, a), (right, b), (output, c))))
    return clauses


def parity_chain(n):
    clauses = xor_gate(1, 2, n + 1)
    previous = n + 1
    for variable in range(3, n + 1):
        output = n + variable - 1
        clauses += xor_gate(previous, variable, output)
        previous = output
    clauses.append((previous,))
    return clauses


def audit_parity():
    chains, marginals, cnf_implicates = [], [], []
    for n in range(2, 7):
        clauses = parity_chain(n)
        assert len(clauses) == 4 * (n - 1) + 1
        total_models = 0
        for point in range(1 << n):
            extensions = sum(satisfies(clauses, point | (auxiliary << n))
                             for auxiliary in range(1 << (n - 1)))
            assert extensions == (point.bit_count() & 1)
            total_models += extensions
        chains.append({"n": n, "clauses": len(clauses), "models": total_models,
                       "minimum_auxiliary_free_cnf_clauses": 1 << (n - 1)})
    for n in range(2, 9):
        comparisons = 0
        for kept_mask in range((1 << n) - 1):
            even_counts, odd_counts = {}, {}
            for point in range(1 << n):
                key = point & kept_mask
                counts = odd_counts if point.bit_count() & 1 else even_counts
                counts[key] = counts.get(key, 0) + 1
            assert even_counts == odd_counts
            assert set(even_counts.values()) == {1 << (n - kept_mask.bit_count() - 1)}
            comparisons += 1
        even = {point for point in range(1 << n) if point.bit_count() % 2 == 0}
        odd = set(range(1 << n)) - even
        assert even & even and not (even & odd)
        marginals.append({"n": n, "proper_subsets_checked": comparisons})
    for n in range(1, 6):
        implicates = 0
        odd = [point for point in range(1 << n) if point.bit_count() & 1]
        for choices in itertools.product((0, 1, -1), repeat=n):
            clause = tuple((i + 1) * sign for i, sign in enumerate(choices) if sign)
            if all(satisfies([clause], point) for point in odd):
                assert len(clause) == n
                assert sum(not satisfies([clause], point) for point in range(1 << n)) == 1
                implicates += 1
        assert implicates == 1 << (n - 1)
        cnf_implicates.append({"n": n, "all_non_tautological_implicates": implicates})
    return {"xor_chain_projection": chains, "proper_marginals": marginals,
            "exhaustive_implicate_check": cnf_implicates}


def poly_xor(*polynomials):
    result = set()
    for polynomial in polynomials:
        result.symmetric_difference_update(polynomial)
    return result


def poly_mul(left, right):
    result = set()
    for a in left:
        for b in right:
            monomial = a | b
            if monomial in result:
                result.remove(monomial)
            else:
                result.add(monomial)
    return result


def poly_evaluate(polynomial, point):
    return sum((monomial & point) == monomial for monomial in polynomial) % 2


def audit_anf():
    comparisons = 0
    for polynomial_mask in range(1 << 8):
        polynomial = {monomial for monomial in range(8) if polynomial_mask & (1 << monomial)}
        for variable in range(3):
            bit = 1 << variable
            a = {monomial for monomial in polynomial if not monomial & bit}
            b = {monomial ^ bit for monomial in polynomial if monomial & bit}
            projected = poly_xor(a, b, poly_mul(a, b))
            for point in range(8):
                expected = poly_evaluate(polynomial, point & ~bit) or poly_evaluate(polynomial, point | bit)
                assert poly_evaluate(projected, point) == expected
                comparisons += 1
    sizes = []
    polynomial = {0}
    for t in range(1, 10):
        x, y = 1 << (2 * t - 2), 1 << (2 * t - 1)
        polynomial = poly_mul(polynomial, {x, y, x | y})
        assert len(polynomial) == 3 ** t
        sizes.append({"disjoint_binary_clauses": t, "expanded_monomials": len(polynomial)})
    return {"projection_comparisons": comparisons, "disjoint_or_expansion": sizes}


def all_affine_systems(n):
    """Enumerate every nonempty affine subspace by intersecting hyperplanes."""
    discovered = {AffineSystem(n)}
    todo = list(discovered)
    while todo:
        system = todo.pop()
        for mask in range(1, 1 << n):
            for rhs in (0, 1):
                result = system.add(mask, rhs)
                if result is not None and result not in discovered:
                    discovered.add(result)
                    todo.append(result)
    return discovered


def audit_affine():
    systems = all_affine_systems(3)
    assert len(systems) == 51
    maximal_or_component = 0
    for system in systems:
        points = {point for point in range(8) if system.contains(point)}
        assert len(points) == 1 << system.dimension
        assert system.witness() in points
        if 0 not in points:
            maximal_or_component = max(maximal_or_component, len(points))
        for variable in range(3):
            projected = system.project(variable)
            bit = 1 << variable
            for point in range(8):
                assert projected.contains(point) == (system.contains(point & ~bit) or system.contains(point | bit))
    assert maximal_or_component == 4
    # Independent full-model semantics, including added XOR constraints.
    rng = random.Random(20260915)
    random_cases = 0
    for n in range(0, 8):
        for _ in range(80):
            clauses = [tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                             for _ in range(rng.randint(0, 3)))
                       for _ in range(rng.randint(0, 12))] if n else [()] * rng.randint(0, 1)
            equations = [(rng.randrange(1 << n), rng.randrange(2))
                         for _ in range(rng.randint(0, 3))]
            result = intersect_cnf(n, clauses, equations=equations)
            assert result.status in ("SAT", "UNSAT")
            expected = {point for point in range(1 << n)
                        if satisfies(clauses, point) and all(((mask & point).bit_count() & 1) == rhs
                                                          for mask, rhs in equations)}
            actual = set()
            for component in result.components:
                points = {point for point in range(1 << n) if component.contains(point)}
                assert not (points & actual), "first-true decomposition must remain disjoint"
                actual.update(points)
            assert actual == expected
            assert (result.status == "SAT") == bool(expected)
            if expected:
                assert result.witness in expected
            random_cases += 1
    growth = []
    for t in range(1, 9):
        clauses = [(3 * i + 1, 3 * i + 2, 3 * i + 3) for i in range(t)]
        start = time.perf_counter()
        result = intersect_cnf(3 * t, clauses)
        elapsed = time.perf_counter() - start
        assert result.status == "SAT" and len(result.components) == 3 ** t
        assert sum(1 << system.dimension for system in result.components) == 7 ** t
        assert max(1 << system.dimension for system in result.components) == 4 ** t
        growth.append({"disjoint_or3_clauses": t, "variables": 3 * t,
                       "explicit_components": len(result.components), "models": 7 ** t,
                       "any_affine_cover_lower_bound": (7 ** t + 4 ** t - 1) // 4 ** t,
                       "gaussian_updates": result.gaussian_updates, "seconds": elapsed})
    cap = intersect_cnf(9, [(1, 2, 3), (4, 5, 6), (7, 8, 9)], max_components=5)
    assert cap.status == "UNKNOWN" and cap.witness is None and not cap.components
    # An explicit affine background makes every OR3 automatic under odd parity.
    mixed = intersect_cnf(30, [(3 * i + 1, 3 * i + 2, 3 * i + 3) for i in range(10)],
                          equations=[(7 << (3 * i), 1) for i in range(10)], max_components=100_000)
    assert mixed.status == "SAT"
    assert sum(1 << state.dimension for state in mixed.components) == 4 ** 10
    return {"all_nonempty_affine_spaces_gf2_3": len(systems),
            "maximum_affine_subset_or3": maximal_or_component,
            "random_full_relation_audits": random_cases, "disjoint_or3_growth": growth,
            "capped_status": cap.status,
            "odd_parity_background_example": {"blocks": 10, "components": len(mixed.components),
                                               "models": 4 ** 10}}


def audit_bdd():
    pairs = []
    for t in range(1, 12):
        orders = {"interleaved": list(range(1, 2 * t + 1)),
                  "blocked": list(range(1, 2 * t + 1, 2)) + list(range(2, 2 * t + 1, 2))}
        sizes = {}
        for name, order in orders.items():
            bdd = BDD(order)
            node = 1
            for i in range(t):
                node = bdd.apply("and", node, bdd.clause((2 * i + 1, 2 * i + 2)))
            if t <= 5:
                for point in range(1 << (2 * t)):
                    assert bdd.evaluate(node, point) == all(point & (3 << (2 * i)) for i in range(t))
            sizes[name] = {"reachable_decision_nodes": bdd.reachable_count(node),
                           "interned_nodes_including_terminals": len(bdd.nodes)}
        assert sizes["interleaved"]["reachable_decision_nodes"] == 2 * t
        assert sizes["blocked"]["reachable_decision_nodes"] >= (1 << t) - 1
        pairs.append({"clauses": t, **sizes})
    rng = random.Random(1729)
    random_cases = 0
    for n in range(1, 8):
        for _ in range(40):
            clauses = [tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                             for _ in range(rng.randint(0, 4)))
                       for _ in range(rng.randint(0, 15))]
            bdd_order, elim_order = list(range(1, n + 1)), list(range(1, n + 1))
            rng.shuffle(bdd_order)
            rng.shuffle(elim_order)
            result = bucket_decide(clauses, bdd_order, elim_order)
            expected = any(satisfies(clauses, point) for point in range(1 << n))
            assert result["status"] == ("SAT" if expected else "UNSAT")
            random_cases += 1
    php = []
    for holes in range(1, 7):
        clauses, rows, columns = pigeonhole(holes)
        for bdd_name, bdd_order, elim_name, elim_order in (
                ("rows", rows, "columns", columns),
                ("rows", rows, "rows", rows),
                ("columns", columns, "columns", columns)):
            start = time.perf_counter()
            result = bucket_decide(clauses, bdd_order, elim_order, max_nodes=500_000)
            elapsed = time.perf_counter() - start
            assert result["status"] == "UNSAT"
            php.append({"holes": holes, "variables": holes * (holes + 1),
                        "clauses": len(clauses), "bdd_order": bdd_name,
                        "elimination_order": elim_name, "seconds": elapsed,
                        **{key: value for key, value in result.items() if key != "steps"}})
    return {"disjoint_binary_or_order_sizes": pairs,
            "random_independent_orders_truth_table_audits": random_cases,
            "pigeonhole_order_experiments": php,
            "interpretation": "Finite implementations reproduce differing costs; Mengel's theorem supplies the asymptotic family result."}


def main():
    started = time.perf_counter()
    result = {"status": "PASS", "python": platform.python_version(),
              "platform": platform.platform(),
              "scope": "Finite independent implementation audits; not a proof of P=NP or universal polynomial complexity."}
    for name, audit in (("local_identity", audit_local_identity), ("parity", audit_parity),
                        ("anf", audit_anf), ("affine_union", audit_affine), ("bdd", audit_bdd)):
        result[name] = audit()
        print(f"PASS {name}", flush=True)
        Path(__file__).with_name("audit_results.json").write_text(json.dumps(result, indent=2) + "\n")
    result["total_seconds"] = time.perf_counter() - started
    Path(__file__).with_name("audit_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"All research audits passed in {result['total_seconds']:.3f}s", flush=True)


if __name__ == "__main__":
    main()
