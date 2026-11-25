"""Finite arithmetic checks for the sharp genuine-CNF group-product bound.

The small graph is a fixture for identities and the direction of inequalities.
It does not simulate the source's asymptotic activation threshold.
"""

from collections import deque
from fractions import Fraction
from itertools import combinations, product
from math import factorial
from random import Random
import json


def fwht(data):
    data = data.copy()
    stride = 1
    while stride < len(data):
        for start in range(0, len(data), 2 * stride):
            for j in range(start, start + stride):
                u, v = data[j], data[j + stride]
                data[j], data[j + stride] = u + v, u - v
        stride *= 2
    return data


def walsh_energy():
    sides = [[0] * 64 for _ in range(3)]
    pairs = list(combinations(range(3), 2))
    joint = {ij: [0] * (64 * 64) for ij in pairs}
    total = 0
    for x in product(range(64), repeat=3):
        if (x[0] ^ x[1]) & 1 or (x[0] ^ x[2]) & 2 or x[0] & 4:
            continue
        total += 1
        for i, letter in enumerate(x):
            sides[i][letter] += 1
        for i, j in pairs:
            joint[i, j][64 * x[i] + x[j]] += 1
    assert total * 8 == 64**3
    means = [fwht(side) for side in sides]
    corr = {ij: fwht(table) for ij, table in joint.items()}
    one_energy = Fraction(sum(x * x for row in means for x in row[1:]), total**2)
    two_energy = sum(
        Fraction(table[64 * a + b] ** 2, total**2)
        for table in corr.values() for a, b in product(range(1, 64), repeat=2)
    )
    assert one_energy + two_energy <= 7
    choices = 0
    passing = 0
    for indices in product(range(1, 64), repeat=3):
        choices += 1
        mean2 = sum(means[i][a] ** 2 for i, a in enumerate(indices))
        off2 = 2 * sum(corr[i, j][64 * indices[i] + indices[j]] ** 2 for i, j in pairs)
        budget = total**2 - 4 * mean2
        if budget >= 0 and 16 * off2 * total**2 <= budget**2:
            passing += 1
    assert passing > 0
    return {
        "alphabet": 64, "coordinates": 3, "density_cap": 8,
        "one_coordinate_energy": str(one_energy),
        "two_coordinate_energy": str(two_energy),
        "nonconstant_contrast_choices": choices,
        "choices_passing_quarter_covariance_defect_test": passing,
    }


def cubic_graph(n, rng):
    half = n // 2
    edges = set()
    for _ in range(3):
        while True:
            right = list(range(half, n))
            rng.shuffle(right)
            layer = set(enumerate(right))
            if edges.isdisjoint(layer):
                edges.update(layer)
                break
    neighbors = [set() for _ in range(n)]
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    assert all(len(vs) == 3 for vs in neighbors)
    seen = {0}
    front = [0]
    while front:
        vertex = front.pop()
        new = neighbors[vertex] - seen
        front.extend(new)
        seen.update(new)
    assert len(seen) == n
    return sorted(edges), neighbors


def maxflow_divergence(edges, demand, capacity):
    n = len(demand)
    start, end = n, n + 1
    residual = [dict() for _ in range(n + 2)]

    def arc(a, b, x):
        residual[a][b] = residual[a].get(b, 0) + x
        residual[b].setdefault(a, 0)

    for a, b in edges:
        arc(a, b, capacity)
        arc(b, a, capacity)
    supply = 0
    for v, d in enumerate(demand):
        if d > 0:
            arc(start, v, d)
            supply += d
        if d < 0:
            arc(v, end, -d)
    delivered = 0
    while True:
        parent = {start: None}
        queue = deque([start])
        while queue and end not in parent:
            a = queue.popleft()
            for b, c in residual[a].items():
                if c > 0 and b not in parent:
                    parent[b] = a
                    queue.append(b)
        if end not in parent:
            break
        v, volume = end, supply
        while v != start:
            a = parent[v]
            volume = min(volume, residual[a][v])
            v = a
        v = end
        while v != start:
            a = parent[v]
            residual[a][v] -= volume
            residual[v][a] += volume
            v = a
        delivered += volume
    assert delivered == supply
    flow = [capacity - residual[a][b] for a, b in edges]
    actual = [0] * n
    for (a, b), f in zip(edges, flow):
        assert abs(f) <= capacity
        actual[a] += f
        actual[b] -= f
    assert actual == demand
    return [Fraction(f, capacity) for f in flow]


def check_graph():
    n = 64
    rng = Random(47329)
    edges, ngh = cubic_graph(n, rng)
    cuts = [{v for v in range(n) if v & (1 << i)} for i in range(3)]
    # Majority of three independent sign characters, repeated on the vertices.
    demand = [1 if sum(v in s for s in cuts) >= 2 else -1 for v in range(n)]
    assert sum(demand) == 0
    cap = 3
    flow = maxflow_divergence(edges, demand, cap)
    conflict = []
    for j, (a, b) in enumerate(edges):
        halo = {a, b} | ngh[a] | ngh[b]
        conflict.append({k for k, e in enumerate(edges) if k != j and halo.intersection(e)})
    p = Fraction(1, 8)
    survival = [p * (1 - p) ** len(js) for js in conflict]
    p_min = min(survival)
    expectations = []
    for s in cuts:
        target = Fraction(sum(demand[v] for v in s), cap)
        predicted = sum(
            ((a in s) - (b in s)) * pe * (p_min * f / pe)
            for (a, b), f, pe in zip(edges, flow, survival)
        )
        assert predicted == p_min * target and target > 0
        expectations.append(str(predicted))
    best = None
    for _ in range(500):
        proposed = {j for j in range(len(edges)) if rng.randrange(8) == 0}
        chosen = [j for j in proposed if conflict[j].isdisjoint(proposed)]
        if not 3 <= len(chosen) <= 7:
            continue
        for signs in product((-1, 1), repeat=len(chosen)):
            imbs = []
            for s in cuts:
                imbs.append(sum(
                    z * ((edges[j][0] in s) - (edges[j][1] in s))
                    for j, z in zip(chosen, signs)
                ))
            if best is None or min(imbs) > best[0]:
                best = min(imbs), chosen, signs, imbs
    assert best and best[0] > 0
    _, indices, orientation, imbs = best
    matched = [edges[j] for j in indices]
    vertices = {v for e in matched for v in e}
    assert {e for e in edges if set(e) <= vertices} == set(matched)
    m = len(matched)
    # Verify all entries of the restricted true count against the OR product.
    assignments = list(product((0, 1), repeat=m))
    rows = [[0] * len(assignments) for _ in assignments]
    for left, x in enumerate(assignments):
        for right, y in enumerate(assignments):
            bits = [1] * n
            for (a, b), xx, yy in zip(matched, x, y):
                bits[a], bits[b] = xx, yy
            cover = int(all(bits[a] or bits[b] for a, b in edges))
            assert cover == int(all(xx or yy for xx, yy in zip(x, y)))
            rows[left][right] = cover
    for j in range(m):
        mask = 1 << j
        for low in range(1 << m):
            if low & mask:
                continue
            high = low ^ mask
            before, after = rows[low], rows[high]
            rows[low], rows[high] = [y - x for x, y in zip(before, after)], before
    assert all(x == int(i == j) for i, row in enumerate(rows) for j, x in enumerate(row))
    return {
        "vertices": n, "edges": len(edges), "source_wires_if_reduced": 10 * n,
        "cut_count": len(cuts), "exact_expected_cut_imbalances": expectations,
        "matched_edges": matched, "orientation": list(orientation),
        "realized_positive_cut_imbalances": imbs,
        "restricted_assignments_checked": 4**m,
        "identity_matrix_dimension": 2**m,
    }


def transfer_and_code():
    valuations = []
    for a in range(1, 9):
        length = 1 << a
        denom = factorial(length) * factorial(length - 1)
        val = (denom & -denom).bit_length() - 1
        top = (a + 1) * (2 * length - 1) - val
        assert top == 2 * a * length + 1
        valuations.append(top)
    # The binary [7,3,4] simplex code. Projection kernels need not be zero.
    code = [sum((((a & i).bit_count() & 1) << (i - 1)) for i in range(1, 8))
            for a in range(8)]
    checked = 0
    maxdiag = 0
    for arg in product(range(3), repeat=7):
        if any(arg.count(i) < 2 for i in range(3)):
            continue
        masks = [sum(1 << j for j, v in enumerate(arg) if v == i) for i in range(3)]
        kernel_sum = {0}
        for m in masks:
            ker = [v for v in code if not v & m]
            kernel_sum = {k ^ l for k in kernel_sum for l in ker}
        w = [0]
        total = set(kernel_sum)
        for c in code:
            if c not in total:
                w += [z ^ c for z in w]
                total |= {z ^ c for z in total}
        for a, b, c in product(w, repeat=3):
            actual = ((a & masks[0]) | (b & masks[1]) | (c & masks[2])) in code
            assert actual == (a == b == c)
        checked += 1
        maxdiag = max(maxdiag, len(w))
    assert maxdiag > 1
    return {"top_shift_valuations_a1_through_a8": valuations,
            "simplex_code_three_group_partitions": checked,
            "largest_restricted_diagonal_side": maxdiag}


if __name__ == "__main__":
    print(json.dumps({"walsh": walsh_energy(), "graph": check_graph(),
                      "transfer_and_code": transfer_and_code()}, indent=2))
