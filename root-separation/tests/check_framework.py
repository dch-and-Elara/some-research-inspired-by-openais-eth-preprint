"""Exact finite checks for the origin, centered-jet and Hermite identities."""

from fractions import Fraction as F
from itertools import combinations, product
from math import ceil, comb, isqrt, prod
from random import Random
import json


def valuation(n):
    if not n:
        raise ValueError("valuation of zero")
    if isinstance(n, F):
        return valuation(n.numerator) - valuation(n.denominator)
    n = abs(n)
    return (n & -n).bit_length() - 1


def mod(value, p):
    value = F(value)
    return value.numerator * pow(value.denominator, -1, 1 << p) % (1 << p)


def mul(f, g, limit=None):
    out = [F(0)] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            out[i + j] += x * y
    return out if limit is None else out[:limit]


def evalpoly(coefficients, value):
    total = 0
    for coefficient in reversed(coefficients):
        total = total * value + coefficient
    return total


def shift(coefficients, t, scale):
    out = [F(0)] * len(coefficients)
    for j, c in enumerate(coefficients):
        for k in range(j + 1):
            out[k] += c * comb(j, k) * t ** (j - k) * scale**k
    return out


def check_real_cnf():
    # Cubic K4 and six-vertex triangular prism, both with genuine signed units.
    fixtures = [
        (4, list(combinations(range(4), 2))),
        (6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5),
             (0, 3), (1, 4), (2, 5)]),
    ]
    checked = 0
    for n, edges in fixtures:
        assert all(sum(v in edge for edge in edges) == 3 for v in range(n))
        incidence_count = n + 2 * len(edges)
        assert 2 * (incidence_count + n) == 10 * n
        assignments = list(product((0, 1), repeat=n))
        for signs in assignments:
            expected = int(all(signs[v] or signs[w] for v, w in edges))
            count = sum(
                all(x[v] == signs[v] for v in range(n))
                and all(x[v] or x[w] for v, w in edges)
                for x in assignments
            )
            assert count == expected
            checked += 1
    # Over a 12-cycle prism the following six-vertex set induces a 3-matching.
    n = 12
    edges = {tuple(sorted((layer * n + v, layer * n + (v + 1) % n)))
             for layer in (0, 1) for v in range(n)}
    edges |= {(v, v + n) for v in range(n)}
    matching = [(0, n), (4, n + 4), (8, n + 8)]
    ends = {v for pair in matching for v in pair}
    assert {e for e in edges if set(e) <= ends} == set(matching)
    checks = 0
    for signs_m in product((0, 1), repeat=6):
        sig = [1] * (2 * n)
        for pair, left, right in zip(matching, signs_m[::2], signs_m[1::2]):
            sig[pair[0]], sig[pair[1]] = left, right
        count = all(sig[v] or sig[w] for v, w in edges)
        assert count == all(sig[v] or sig[w] for v, w in matching)
        checks += 1
    return {"enumerated_signed_cnfs": checked,
            "induced_matching_assignments": checks, "physical_wires_per_vertex": 10}


def gf2_rank(rows):
    pivots = {}
    for v in rows:
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                v ^= pivots[p]
            else:
                pivots[p] = v
                break
    return len(pivots)


def matching_rank_check():
    rng = Random(62791)
    counts = 0
    for n in range(1, 6):
        xs = list(product((0, 1), repeat=n))
        target = [sum(1 << j for j, y in enumerate(xs)
                      if all(a or b for a, b in zip(x, y))) for x in xs]
        assert gf2_rank(target) == 2**n
        for _ in range(60):
            p = {j for j in range(2 * n) if rng.randrange(2)}
            if not p or len(p) == 2 * n:
                continue
            first = sorted(p)
            second = sorted(set(range(2 * n)) - p)
            f = {s: rng.randrange(2) for s in product((0, 1), repeat=len(first))}
            g = {s: rng.randrange(2) for s in product((0, 1), repeat=len(second))}
            rows = []
            for x in xs:
                row = 0
                for j, y in enumerate(xs):
                    bits = x + y
                    value = f[tuple(bits[k] for k in first)] & g[tuple(bits[k] for k in second)]
                    row |= value << j
                rows.append(row)
            a = sum(j < n for j in p)
            b = len(p) - a
            assert gf2_rank(rows) <= 2 ** (n - abs(a - b))
            counts += 1
    return {"invertible_or_tensor_sizes": [2, 4, 8, 16, 32], "tested_separated_terms": counts}


def majority_check():
    reports = []
    for r, depth in ((2, 4), (3, 3), (4, 3), (5, 2)):
        labels = list(product(range(r), repeat=depth))
        d = [[0] * r for _ in range(depth)]
        abs_total = 0
        for a, b in product(labels, repeat=2):
            difference = sum(int(x != r - 1) - int(y != r - 1) for x, y in zip(a, b))
            signed = (difference > 0) - (difference < 0)
            abs_total += abs(difference)
            for j in range(depth):
                d[j][a[j]] += signed
                d[j][b[j]] -= signed
        minimal = None
        for ds in d:
            assert ds[:r-1] == [abs_total // (depth * (r-1))] * (r-1)
            assert ds[-1] == -sum(ds[:-1])
            for m in range(1, (1 << r) - 1):
                deviation = abs(sum(v for i, v in enumerate(ds) if m & (1 << i)))
                minimal = deviation if minimal is None else min(minimal, deviation)
        assert minimal * depth * (r-1) == abs_total
        reports.append({"symbols": r, "coordinates": depth, "ordered_edges": len(labels)**2,
                        "minimum_imbalance": minimal})
    return reports


def bang_check():
    rng = Random(7321)
    tested = 0
    for k in range(1, 8):
        for _ in range(12):
            rows = [tuple(rng.choice((-1, 0, 1)) for _ in range(18)) for j in range(k)]
            candidates = []
            for signs in product((-1, 1), repeat=k):
                y = [sum(s * row[e] for s, row in zip(signs, rows)) for e in range(18)]
                candidates.append((sum(a*a for a in y), signs, y))
            _, signs, y = max(candidates)
            assert all(s * sum(a*b for a, b in zip(row, y)) >= sum(a*a for a in row)
                       for s, row in zip(signs, rows))
            tested += 1
    return {"palettes_checked_at_sign_maximum": tested}


def smooth_potential_check():
    """Check a rational Huber analogue at a global sign maximizer.

    Scale all vertex weights to a common integer denominator. The objective,
    flip comparisons, correlations and lower bounds then use integer arithmetic.
    """
    results = []
    for k, r in ((2, 4), (3, 3)):
        labels = list(product(range(r), repeat=k))
        loads = [1 + 2 * int(x[0] == x[-1]) + int(sum(x) % 3 == 1) for x in labels]
        n = sum(loads)
        cuts = [(i, g) for i in range(k) for g in range(r)]
        masses = [sum(c for x, c in zip(labels, loads) if x[i] == g) for i, g in cuts]
        features = [[(n if x[i] == g else 0) - mass for (i, g), mass in zip(cuts, masses)]
                    for x in labels]
        eta = F(min(min(p, n-p) for p in masses), n)
        density_cap = F(max(loads) * len(labels), n)
        threshold_squared = density_cap * k * r*r
        h = isqrt(ceil(threshold_squared))
        if h*h < threshold_squared:
            h += 1
        scale = n * h
        def objective(signs):
            y = [sum(v * s for v, s in zip(row, signs)) for row in features]
            # Twice ρ(y/scale) multiplied by scale², with clipping at 4.
            value = sum(c * (t*t if abs(t) <= 4*scale else 8*scale*abs(t)-16*scale*scale)
                        for c, t in zip(loads, y))
            return value, signs, y
        maximum, signs, y = max(objective(s) for s in product((-1, 1), repeat=len(cuts)))
        assert sum(c*t*t for c, t in zip(loads, y)) <= n * scale*scale
        bounded = [min(4*scale, max(-4*scale, t)) for t in y]
        correlations = []
        for j, s in enumerate(signs):
            flipped = list(signs)
            flipped[j] = -s
            assert objective(flipped)[0] <= maximum
            corr = F(sum(c*b*row[j] for c, b, row in zip(loads, bounded, features)),
                     4 * n*n * scale)
            assert s*corr >= F(3, 16*h)*eta*eta
            correlations.append(abs(corr))
        results.append({"symbols": r, "coordinates": k, "balanced_events": len(cuts),
                        "distinct_labels": len(labels), "total_label_mass": n,
                        "domination_C": str(density_cap), "integer_H": h,
                        "minimum_observed_correlation": str(min(correlations)),
                        "certified_lower_bound": str(F(3, 16*h)*eta*eta)})
    return results


def jet_checks():
    length = 16
    grid = list(range(-length, length))
    alpha = 2 * length
    p, q = 117, 20
    b = ceil(p / q)
    d = (length.bit_length() - 1) + 1 + b + 16 * 2
    denom = prod(-j for j in grid if j)
    kernels = lifts = 0
    for t in (-7, -4, -2, 1, 4, 8):
        i = valuation(t)
        group_slots = [j for j in range(length) if not (j & (1 << i))]
        rows = group_slots[:3]
        cols = group_slots[:2]
        T = t + alpha * (1 << b)
        A = F(prod(T - j for j in grid), denom)
        assert valuation(A) == length.bit_length() + b
        for x, y in product(rows, cols):
            polynomial = [F(1, denom)]
            for j in grid:
                if j != y - x:
                    polynomial = mul(polynomial, [F(t - j), F(alpha)])
            assert all(c == 0 or valuation(c) >= 0 for c in polynomial)
            full = A / (T + x - y)
            assert evalpoly(polynomial, 1 << b) == full
            assert mod(evalpoly(polynomial[:q], 1 << b), p) == mod(full, p)
            kernels += 1
        for selected in combinations(rows, 2):
            for y in cols:
                coeffs = []
                for x in selected:
                    bx = T + x
                    numerator = prod(bx - j for j in cols) * prod(y - T - z for z in selected if z != x)
                    denominator = A * prod(y - j for j in cols if j != y) * prod(x - z for z in selected if z != x)
                    coeffs.append(F(numerator, denominator))
                assert all(c == 0 or valuation((1 << d) * c) >= 0 for c in coeffs)
                for bits in product((0, 1), repeat=2):
                    forms = [A * sum(F(v, T + x - j) for j, v in zip(cols, bits)) for x in selected]
                    recovered = sum(c * z for c, z in zip(coeffs, forms))
                    assert recovered == bits[cols.index(y)]
                    scaled_mod = sum(mod((1 << d) * c, p) * mod(z, p) for c, z in zip(coeffs, forms))
                    assert scaled_mod % (1 << p) == ((1 << d) * bits[cols.index(y)]) % (1 << p)
                    lifts += 1
    return {"nonunit_shift": 1 << b, "precision": p, "jet_length": q,
            "true_grid_kernel_congruences": kernels, "inverse_cauchy_bit_identities": lifts}


def hermite_at_zero(f, multiplicities, alpha):
    total = F(0)
    for t, q in multiplicities.items():
        basis = [F(1)]
        for other, h in multiplicities.items():
            if t != other:
                for _ in range(h):
                    basis = mul(basis, [F(-other, t-other), F(1, t-other)])
        at_t = shift(basis, t, alpha)
        assert at_t[0] == 1
        numerator = shift(f, t, alpha)
        quotient = []
        for j in range(q):
            value = numerator[j] if j < len(numerator) else F(0)
            quotient.append(value - sum(at_t[k] * quotient[j-k] for k in range(1, min(j+1, len(at_t)))))
        total += basis[0] * evalpoly(quotient, F(-t, alpha))
    return total


def even_hermite_checks():
    capacity_checks = loss_checks = 0
    for u in range(6, 10):
        L = 1 << u
        for M in (u, 2*u+1, 57):
            h = (3 * M + u - 1) // u
            qt = {t: h * (u-valuation(t)) for t in range(-L, L)
                  if t and valuation(t) < u}
            even = {t: q for t, q in qt.items() if t % 2 == 0}
            total = sum(even.values())
            assert total == h * L * (u - 2 + F(1, 1 << (u-1)))
            assert total > M * (2*L-1)
            capacity_checks += 1
            for t in (-2, 4, 6):
                def loss(mults):
                    return sum(q * (valuation(s) - valuation(t - s))
                               for s, q in mults.items() if t != s)
                assert loss(qt) == loss(even)
                loss_checks += 1
    rng = Random(111)
    full = {-3: 2, -2: 3, -1: 2, 1: 2, 2: 3, 3: 2}
    even = {-2: 3, 2: 3}
    for _ in range(8):
        f = [F(rng.randrange(-15, 16), rng.choice((1, 3, 5))) for j in range(6)]
        assert hermite_at_zero(f, even, 8) == hermite_at_zero(f, full, 8) == f[0]
    return {"source_shape_capacity_checks": capacity_checks, "loss_equalities": loss_checks,
            "full_vs_even_exact_polynomial_recoveries": 8}


if __name__ == "__main__":
    result = {
        "genuine_cnf": check_real_cnf(), "flattenings": matching_rank_check(),
        "common_orientation": majority_check(), "bang": bang_check(),
        "smooth_common_correlations": smooth_potential_check(),
        "direct_jets": jet_checks(), "even_center_recovery": even_hermite_checks(),
    }
    print(json.dumps(result, indent=2))
