"""Exact finite checks for node-dependent actual-incidence reconstruction.

Only the Python standard library is required. All ranks use integer elimination
with primitive row reduction, so no floating-point or modular-rank assumption
enters any comparison.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, gcd, prod
import json
import random


def subsets(items, minimum=0):
    items = tuple(items)
    for size in range(minimum, len(items) + 1):
        yield from combinations(items, size)


def rank(rows):
    basis = {}
    for incoming in rows:
        row = list(incoming)
        for j, value in enumerate(row):
            if not value:
                continue
            if j not in basis:
                divisor = 0
                for entry in row[j:]:
                    divisor = gcd(divisor, entry)
                basis[j] = [x // divisor for x in row]
                break
            pivot = basis[j]
            p = pivot[j]
            common = gcd(value, p)
            a, b = p // common, value // common
            for t in range(j, len(row)):
                row[t] = a * row[t] - b * pivot[t]
            divisor = 0
            for entry in row[j + 1 :]:
                divisor = gcd(divisor, entry)
            if divisor > 1:
                for t in range(j + 1, len(row)):
                    row[t] //= divisor
    return len(basis)


@lru_cache(maxsize=None)
def phi(degree, mismatches):
    return Fraction(
        sum(comb(mismatches, j) * max(0, mismatches - degree - 2 * j)
            for j in range(mismatches + 1)),
        2 ** mismatches,
    )


def random_layout(rng, variables, nodes, degree):
    """Generate a feasible rational P first and determine minimal group maps."""
    groups = rng.randint(2, min(4, variables + 1))
    a = [[rng.randrange(groups) for _ in range(variables)] for _ in range(nodes)]
    b = [[rng.randrange(groups) for _ in range(variables)] for _ in range(nodes)]
    values = [[[0] * variables for _ in range(variables)] for _ in range(nodes)]
    scale = factorial(nodes)
    for u in range(variables):
        roots = rng.sample(range(1, nodes + 1), rng.randint(0, degree))
        unused_degree = degree - len(roots)
        for v in range(variables):
            coefficients = [int(u == v)]
            coefficients.extend(rng.choice([-1, 0, 0, 0, 1])
                                for _ in range(unused_degree))
            for t in range(1, nodes + 1):
                polynomial = sum(c * t**i for i, c in enumerate(coefficients))
                values[t-1][u][v] = (
                    (scale // prod(roots)) * prod(root-t for root in roots)
                    * polynomial
                )
    # values[t-1] = nodes! * P(t), an invertible constant scalar times P(t).
    # Each group's projected foreign rows form its smallest allowable row space.
    measurements = []
    for t in range(nodes):
        at_node = []
        for g in range(groups):
            group_rows = []
            for u in range(variables):
                if b[t][u] == g:
                    continue
                row = [values[t][u][v] if a[t][v] == g else 0
                       for v in range(variables)]
                if any(row):
                    group_rows.append(row)
            at_node.append(group_rows)
        measurements.append(at_node)
    return a, b, measurements, values


def group_image(rows, vertices):
    """Exact reachable tuples after setting all unchosen variables to zero."""
    result = set()
    for bits in product((0, 1), repeat=len(vertices)):
        result.add(tuple(sum(row[v]*bit for v, bit in zip(vertices, bits))
                         for row in rows))
    return len(result)


def check_node_subsets(layout, degree, counters):
    a, b, maps, values = layout
    nodes, variables = len(a), len(a[0])
    for vertices in subsets(range(variables), 1):
        ranks, nonzero_columns, cut_defects, nullities = [], [], [], []
        for t, group_maps in enumerate(maps):
            measured_rank = 0
            nonzero = 0
            for g, rows in enumerate(group_maps):
                local = [v for v in vertices if a[t][v] == g]
                restricted = [[row[v] for v in local] for row in rows]
                current_rank = rank(restricted)
                current_nonzero = sum(any(row[v] for row in rows) for v in local)
                image_size = group_image(rows, local)
                assert image_size >= max(2**current_rank, current_nonzero + 1)
                measured_rank += current_rank
                nonzero += current_nonzero
                counters["restricted_group_image_checks"] += 1
            ranks.append(measured_rank)
            nonzero_columns.append(nonzero)
            size_differences = [
                sum(a[t][v] == g for v in vertices)
                - sum(b[t][v] == g for v in vertices)
                for g in range(len(group_maps))
            ]
            cut_defects.append(sum(abs(x) for x in size_differences) // 2)
            minor = [[values[t][u][v] for v in vertices] for u in vertices]
            nullities.append(len(vertices) - rank(minor))
            assert nullities[-1] >= cut_defects[-1] - measured_rank
        for points in subsets(range(nodes), 1):
            assert sum(nullities[t] for t in points) <= degree * len(vertices)
            assert sum(cut_defects[t]-ranks[t] for t in points) <= (
                degree * len(vertices)
            )
            counters["principal_minor_and_imbalance_checks"] += 1
            if len(points) <= degree:
                continue
            mismatches = [sum(a[t][v] != b[t][v] for t in points)
                          for v in vertices]
            lower = 2 * sum(phi(degree, h) for h in mismatches)
            actual = sum(ranks[t] for t in points)
            assert actual >= lower, (points, vertices, degree, actual, lower)
            assert sum(nonzero_columns[t] for t in points) >= (
                sum(mismatches) - len(vertices)*degree
            )
            counters["physical_node_variable_subset_checks"] += 1
            if actual == lower and lower > 0:
                counters["positive_tight_rank_checks"] += 1


def tensor_vector(factors):
    values = [1]
    for factor in factors:
        values = [x*y for x in values for y in factor]
    return values


def check_filtration(layout, degree, counters):
    a, b, maps, _ = layout
    nodes, variables = len(a), len(a[0])
    target_degree = nodes - degree - 1
    dimension = 2**nodes
    ranks_at_nodes = [sum(rank(rows) for rows in pack) for pack in maps]
    maximum_cost = dimension * sum(ranks_at_nodes) // 2
    previous_kernel = 0
    previous_space = 0
    for j in range(target_degree + 1):
        columns = []
        forced = 0
        for v in range(variables):
            matched = {t for t in range(nodes) if a[t][v] == b[t][v]}
            for support_tuple in subsets(range(nodes)):
                support = set(support_tuple)
                if len(support) > j:
                    continue
                dual = matched.symmetric_difference(support)
                forced += len(dual) <= target_degree - j
                factors = []
                for t in range(nodes):
                    if t not in support:
                        factors.append((1, a[t][v]+1))
                    elif t in matched:
                        factors.append((0, 1))
                    else:
                        factors.append((1, b[t][v]+1))
                tensor = tensor_vector(factors)
                for exponent in range(j-len(support)+1):
                    column = []
                    for t in range(nodes):
                        scalar = (t+1)**exponent * prod(t-s for s in support)
                        for rows in maps[t]:
                            for row in rows:
                                column.extend(scalar * row[v] * x for x in tensor)
                    columns.append(column)
        evaluated_rank = rank(columns)
        kernel = len(columns) - evaluated_rank
        assert evaluated_rank <= maximum_cost
        assert kernel-previous_kernel <= len(columns)-previous_space-forced
        previous_kernel, previous_space = kernel, len(columns)
        counters["exact_tensor_filtration_levels"] += 1


def check_gate_extension(counters):
    for n in range(2, 5):
        candidates = tuple(combinations(range(n), 2))
        for edges in subsets(candidates):
            for bits in product((0, 1), repeat=n):
                count = 0
                for fresh in product((0, 1), repeat=len(edges)):
                    ok = all((not y or bits[u]) and (not y or bits[v]) and
                             (y or not bits[u] or not bits[v])
                             for (u, v), y in zip(edges, fresh))
                    if ok:
                        assert all(y == bits[u]*bits[v]
                                   for (u, v), y in zip(edges, fresh))
                        count += 1
                assert count == 1
                counters["original_assignments_with_unique_gate_extension"] += 1


def main():
    rng = random.Random(20261125)
    counters = {
        "feasible_polynomial_layouts": 0,
        "physical_node_variable_subset_checks": 0,
        "positive_tight_rank_checks": 0,
        "restricted_group_image_checks": 0,
        "principal_minor_and_imbalance_checks": 0,
        "exact_tensor_filtration_levels": 0,
        "original_assignments_with_unique_gate_extension": 0,
    }
    for n, q in ((2, 2), (3, 3), (4, 4), (4, 5), (5, 6)):
        for degree in range(q):
            for sample in range(8):
                layout = random_layout(rng, n, q, degree)
                check_node_subsets(layout, degree, counters)
                if q <= 4 and n <= 4 and sample < 2:
                    check_filtration(layout, degree, counters)
                counters["feasible_polynomial_layouts"] += 1
    check_gate_extension(counters)
    print(json.dumps({"status": "passed", "seed": 20261125, **counters},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
