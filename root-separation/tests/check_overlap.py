"""Exact reduced fixtures for the native support, scope capacity, and uniform transfers."""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb, prod
import json
import random


def bits(number, size):
    return tuple((number >> i) & 1 for i in range(size))


def field_rank(matrix, prime):
    rows = [[a % prime for a in row] for row in matrix]
    rank = 0
    for column in range(len(rows[0])):
        pivot = next((j for j in range(rank, len(rows)) if rows[j][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][column], -1, prime)
        rows[rank] = [(x * inv) % prime for x in rows[rank]]
        for j in range(rank + 1, len(rows)):
            factor = rows[j][column]
            rows[j] = [(x - factor * y) % prime for x, y in zip(rows[j], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def matching(edges, side):
    for size in reversed(range(side + 1)):
        for lefts in combinations(range(side), size):
            for rights in permutations(range(side, 2 * side), size):
                selected = tuple(zip(lefts, rights))
                if all(e in edges for e in selected):
                    return selected


def capacity_fixtures():
    side, rng = 3, random.Random(412352)
    all_edges = [(i, j) for i in range(side) for j in range(side, 2 * side)]
    partitions = Counter()
    for mask in range(1 << len(all_edges)):
        edges = [edge for j, edge in enumerate(all_edges) if mask >> j & 1]
        route = matching(edges, side)
        cover = min(c.bit_count() for c in range(1 << (2 * side))
                    if all((c >> i | c >> j) & 1 for i, j in edges))
        assert cover == len(route)
        partitions[cover] += 1
        weights = {edge: [rng.randrange(5) for _ in range(4)] for edge in edges}
        lower, generic = [], []
        for a in range(1 << side):
            lo, gen = [], []
            for b in range(1 << side):
                x = bits(a, side) + bits(b, side)
                lo.append(int(all(x[i] == x[j] for i, j in route)))
                gen.append(prod(weights[i, j][x[i] + 2 * x[j]] for i, j in edges))
            lower.append(lo)
            generic.append(gen)
        assert field_rank(lower, 2) == 2**cover
        assert field_rank(generic, 5) <= 2**cover
    allvars, left = set(range(2 * side)), set(range(side))
    right = allvars - left
    checked = 0
    for pcode, ocode in product(range(1 << (2 * side)), repeat=2):
        p = {i for i in allvars if pcode >> i & 1}
        q = allvars - p
        if len(p & left) < len(p & right):
            p, q = q, p
        overlap = {i for i in allvars if ocode >> i & 1}
        v1, v2 = p | overlap, q | overlap
        edges = [(i, j) for i, j in all_edges if {i, j} <= v1 or {i, j} <= v2]
        imbalance = len(p & left) - len(p & right)
        hazard = len(left & p & overlap) + len(right & q & overlap)
        assert len(matching(edges, side)) == side - max(0, imbalance - hazard)
        checked += 1
    return {"binary_bipartite_graphs": 512, "matching_histogram": dict(partitions),
            "two_view_base_and_overlap_pairs": checked}


def latent_fixtures():
    rng = random.Random(1472)
    sizes = [1, 1, 1, 1, 2, 1]
    clones = [(i, j) for i, b in enumerate(sizes) for j in range(b)]
    left, right = {c for c in clones if c[0] < 2}, {c for c in clones if 2 <= c[0] < 4}
    trials = Counter()
    for _ in range(120):
        scopes = [set([i]) for i in range(6)]
        scopes.extend(set(rng.sample(range(6), rng.choice([2, 2, 3])))
                      for _ in range(rng.randint(2, 6)))
        adjacent = {c: set() for c in clones}
        for c, d in combinations(clones, 2):
            if c[0] != d[0] and any({c[0], d[0]} <= s for s in scopes):
                adjacent[c].add(d)
                adjacent[d].add(c)
        paths = []
        def explore(path):
            if path[-1] in right:
                paths.append(tuple(path))
                return
            for nxt in adjacent[path[-1]] - set(path) - left:
                explore(path + [nxt])
        for start in sorted(left):
            explore([start])
        paths.sort()
        route = next(((p, q) for p in paths for q in paths if set(p).isdisjoint(q)),
                     (paths[0],) if paths else ())
        cap = min(sum(b for i, b in enumerate(sizes) if mask >> i & 1)
                  for mask in range(1 << len(sizes))
                  if all(any(mask >> v & 1 for v, _ in path) for path in paths))
        assert cap == len(route)
        trials[cap] += 1
        assignments = [[] for _ in scopes]
        used = set()
        for path in route:
            used.update(path)
            for c, d in zip(path, path[1:]):
                witness = next(i for i, s in enumerate(scopes) if {c[0], d[0]} <= s)
                assignments[witness].append((c, d))
        for v, j in clones:
            if v >= 4 and (v, j) not in used:
                assignments[v].append(((v, j), None))
        shape = []
        for x, y in product(range(4), repeat=2):
            mass = 0
            for z, t in product(range(4), range(2)):
                vals = bits(x, 2) + bits(y, 2) + (z, t)
                def bit(c):
                    return 0 if c is None else (vals[c[0]] >> c[1]) & 1
                mass += prod(all(bit(c) == bit(d) for c, d in checks)
                             for checks in assignments)
            shape.append(mass)
        assert field_rank([shape[j:j+4] for j in range(0, 16, 4)], 2) == 2**cap
    return {"mixed_one_and_two_bit_domain_trials": sum(trials.values()),
            "min_vertex_capacity_histogram": dict(trials)}


def kernel(length, center, lift, precision):
    modulus = 1 << precision
    grid = list(range(-length, length))
    denominator = prod(-q for q in grid if q != 0)
    t = center + 2 * length * lift
    def entry(x, y):
        value = Fraction(prod(t - q for q in grid if q != y - x), denominator)
        assert value.denominator % 2
        return value.numerator * pow(value.denominator, -1, modulus) % modulus
    return [[entry(x, y) for y in range(length)] for x in range(length)]


def support_fixtures():
    width, selected, precision = 4, 4, 40
    modulus = 1 << precision
    labels = [sum(1 << j for j in subset)
              for subset in combinations(range(selected), selected // 2)]
    values = kernel(width, 1, 1, precision)
    coefficients = [values[0][0], values[2][0], values[0][2], values[2][2]]
    assert all((v & -v) == 8 for v in coefficients)
    pair = {(s, t): prod(coefficients[j] * (t >> j & 1)
                          for j in range(selected) if s >> j & 1) % modulus
            for s in labels for t in labels}
    positive = 0
    for s0, t0, s1, t1, s2, t2 in product(labels, repeat=6):
        ans = pair[s0, t0] * pair[s1, t1] * pair[s2, t2] % modulus
        assert bool(ans) == (s0 == t0 and s1 == t1 and s2 == t2)
        positive += bool(ans)
    p = 4
    sound, maxdiagonal = 0, 0
    for uv in product(range(p+1), repeat=6):
        u, v = uv[:3], uv[3:]
        if any(u[i]+v[j]<p for i in range(3) for j in range(3) if i!=j):
            continue
        sound += 1
        maxdiagonal = max(maxdiagonal, sum(u[i]+v[i]<p for i in range(3)))
    assert maxdiagonal == 1
    return {"raw_group_count": 3, "raw_half_edge_inputs": len(labels)**6,
            "positive_inputs": positive, "antichain_alphabet": len(labels),
            "valuations_per_side_pairs_checked": (p+1)**6,
            "sound_pairs": sound, "max_sound_diagonal": maxdiagonal}


def packing_fixtures():
    stats = []
    for r, a in ((3, 1), (3, 2), (2, 3)):
        length = 2**a
        labels = list(product(range(r), repeat=a))
        queues = {key: deque(range(j*length, (j+1)*length))
                  for j, key in enumerate(product(labels, repeat=2))}
        n = len(queues) * length
        loads, wires = Counter(), set()
        count = 0
        for sig in product(combinations_with_replacement(range(r), 2), repeat=a):
            g = 2**sum(v == w for v, w in sig)
            for _ in range(length // g):
                count += 1
                for h in range(length):
                    row = tuple(s[(h >> j) & 1] for j, s in enumerate(sig))
                    col = tuple(s[1-((h >> j) & 1)] for j, s in enumerate(sig))
                    comp = queues[row, col].popleft()
                    for w in [2*comp, 2*comp+1]:
                        assert w not in wires
                        wires.add(w)
                        loads[row, col] += 1
        assert len(wires) == 2*n and all(not q for q in queues.values())
        assert set(loads.values()) == {2*length} and 2*count == 2*n//length
        stats.append({"symbols": r, "coordinates": a, "components": n,
                      "packet_pairs": count, "common_ordered_load": 2*length})
    return stats


def basis(bit, value):
    return value if bit else 1-value


def evalrow(table, v, w):
    return sum(table[b+2*c] * basis(b, v) * basis(c, w)
               for b,c in product(range(2), repeat=2))


def transfers():
    rng = random.Random(4135)
    modulus = 1 << 24
    wk = kernel(2, 1, 1, 24)
    def random_table(arity):
        table = [rng.randrange(2) for _ in range(2**arity)]
        table[rng.randrange(len(table))] = 1
        return table
    def arg(bits_in, pairs):
        vals = [None] * len(bits_in)
        for pair in pairs:
            for i, pos in enumerate(pair):
                vals[pos] = sum(wk[i][j]*bits_in[k] for j,k in enumerate(pair)) % modulus
        return vals
    pair_checks = 0
    for _ in range(70):
        rows = [random_table(2) for _ in range(2)]
        cols = [random_table(1) for _ in range(4)]
        exact, via = 0, 0
        for x in product(range(2), repeat=4):
            col = prod(q[b] for q,b in zip(cols,x))
            v = arg(x, [(0,1),(2,3)])
            via += col * prod(evalrow(rows[j],v[j],v[j+2]) for j in range(2))
            for y in product(range(2), repeat=4):
                exact += col * prod(rows[j][y[j]+2*y[j+2]] for j in range(2)) * prod(
                    basis(b, z) for b,z in zip(y,v))
        assert exact % modulus == via % modulus
        pair_checks += 1
    def interval_factors(t, x, incoming, v):
        return (t[0][x[0]] * t[1][x[2]+2*x[4]]
                * t[2][x[1]+2*x[3]+4*incoming]
                * prod(evalrow(tab,v[j],v[j+1])
                       for tab,j in zip(t[3:], [0,2,4]))) % modulus
    fixture_pairs = [(0,5),(2,1),(4,3)]
    local = [(x, arg(x,fixture_pairs)) for x in product(range(2),repeat=6)]
    nonidentical, repeated_fails = 0, 0
    for _ in range(32):
        tabs = [[random_table(a) for a in [1,2,3,2,2,2]] for _ in range(2)]
        mats = []
        for t in tabs:
            mats.append([[sum(interval_factors(t, x, d, v) for x,v in local if x[5]==e)
                          % modulus for e in range(2)] for d in range(2)])
        direct = sum(interval_factors(tabs[0],x1,x2[5],v1) *
                     interval_factors(tabs[1],x2,x1[5],v2)
                     for x1,v1 in local for x2,v2 in local) % modulus
        def trace_product(k,l):
            return sum(k[d][e]*l[e][d] for d,e in product(range(2),repeat=2)) % modulus
        assert direct == trace_product(mats[0],mats[1])
        nonidentical += mats[0] != mats[1]
        repeated_fails += direct != trace_product(mats[0],mats[0])
    assert nonidentical > 0 and repeated_fails > 0
    return {"arbitrary_table_companion_literal_sums": pair_checks,
            "arbitrary_table_two_interval_global_column_sums": 32,
            "unequal_transfer_matrices": nonidentical,
            "incorrect_repeated_first_matrix": repeated_fails}


def genuine_cnf_fixture():
    edges = [(i,j) for i,j in combinations(range(8),2) if (i ^ j).bit_count() == 1]
    selected = [(0,1),(6,7)]
    assert {e for e in edges if set(e) <= {0,1,6,7}} == set(selected)
    rows = []
    for a in range(4):
        row = []
        for b in range(4):
            sig = [1]*8
            for h,(i,j) in enumerate(selected):
                sig[i], sig[j] = a >> h & 1, b >> h & 1
            count = sum(all(assignment[v] == sig[v] for v in range(8))
                        and all(assignment[i] or assignment[j] for i,j in edges)
                        for assignment in product(range(2), repeat=8))
            assert count == prod(sig[i] or sig[j] for i,j in selected)
            row.append(count)
        rows.append(row)
    assert field_rank(rows,2) == 4
    return {"cubic_cube_variables": 8, "retained_matching": selected,
            "integral_OR_transversal_rank_mod_2": 4}


if __name__ == "__main__":
    print(json.dumps({"scope_capacity": capacity_fixtures(), "latent_route": latent_fixtures(),
                      "native_masks": support_fixtures(), "companion_packing": packing_fixtures(),
                      "native_transfers": transfers(), "true_cnf": genuine_cnf_fixture()},
                     indent=2, sort_keys=True))
