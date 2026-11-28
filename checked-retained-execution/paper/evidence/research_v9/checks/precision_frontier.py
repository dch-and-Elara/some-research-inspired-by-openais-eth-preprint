"""Exact finite tests for the completed Appendix D root precision theorems.

The small grid parameters exercise the source algebra and packing rules.
They do not claim to be the asymptotic printed parameters at these sizes.
Run from any directory. No third-party dependencies are required.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations_with_replacement, product
import json
from math import comb, isqrt, prod
from pathlib import Path
from random import Random
import sys


def order2(value):
    if not value:
        return float("inf")
    frac = Fraction(value)
    return ((abs(frac.numerator) & -abs(frac.numerator)).bit_length()
            - (frac.denominator & -frac.denominator).bit_length())


def residue(fraction, modulus):
    f = Fraction(fraction)
    assert f.denominator % 2
    return f.numerator * pow(f.denominator, -1, modulus) % modulus


# Exact arithmetic in Q[U]/(U^2+U+1). The minimum coordinate order is
# multiplicative since the defining polynomial is irreducible modulo two.
def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def scale(x, b):
    return x[0] * b, x[1] * b


def multiply(x, y):
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c - b * d


def inverse(x):
    a, b = x
    norm = a * a - a * b + b * b
    return Fraction(a - b, norm), Fraction(-b, norm)


def pair_mod(x, modulus):
    return tuple(residue(c, modulus) for c in x)


def order_pair(x):
    return min(map(order2, x))


@cache
def grid_numerator(a, t, z):
    L = 1 << a
    T = add((t, 0), scale(z, 2 * L))
    numerator = (1, 0)
    for q in range(-L, L):
        numerator = multiply(numerator, add(T, (-q, 0)))
    denominator = prod(-q for q in range(-L, L) if q)
    return scale(numerator, Fraction(1, denominator))


@cache
def kernel(a, t, z, q):
    L = 1 << a
    if z == (0, 0):
        if q != t:
            return (0, 0)
        return (Fraction(prod(t - d for d in range(-L, L) if d != t),
                         prod(-d for d in range(-L, L) if d)), 0)
    denominator = add((t - q, 0), scale(z, 2 * L))
    return multiply(grid_numerator(a, t, z), inverse(denominator))


@cache
def crossing(a, t, z, x, tile, b):
    i = order2(t)
    value = kernel(a, t, z, tile - x)
    denominator = add((t - tile + x, 0), scale(z, 2 << a))
    ratio = scale(inverse(denominator), 2 << i)
    for _ in range(b):
        value = multiply(value, ratio)
    return value


def bit(number, i):
    return (number >> i) & 1


def check_crossings():
    comparisons = 0
    sharp = 0
    zero_checks = 0
    localization = 0
    for a in (2, 4):
        L = 1 << a
        for t in range(-L, L):
            if not t or order2(t) >= a // 2:
                continue
            i = order2(t)
            delta = a + 1 - i
            for x in range(L):
                for tile in range(2 << i):
                    if bit(tile, i) != bit(x, i):
                        continue
                    h = order2(t - tile + x)
                    assert h <= i
                    for b in range(3):
                        cost = delta + b + (b + 1) * (i - h)
                        for z in ((0, 0), (1, 0), (-1, 0), (2, 0),
                                  (0, 1), (1, 1), (0, 2)):
                            raw = crossing(a, t, z, x, tile, b)
                            if z == (0, 0):
                                assert raw == (0, 0)
                                zero_checks += 1
                                continue
                            assert order_pair(raw) == cost + order_pair(z)
                            comparisons += 1
                            if cost == delta + b:
                                sharp += 1
                            if not b:
                                top = pair_mod(scale(raw, Fraction(1, 1 << delta)), 2)
                                expected = pair_mod(z, 2) if x % (2 << i) == tile else (0, 0)
                                assert top == expected
                                localization += 1
    return dict(nonzero_valuation_comparisons=comparisons, sharp_at_universal_cost=sharp,
                zero_probe_checks=zero_checks, singleton_localization_checks=localization)


def qadd(x, y, m):
    return tuple(c % m for c in add(x, y))


def qmul(x, y, m):
    return tuple(c % m for c in multiply(x, y))


def qscale(x, b, m):
    return tuple(c % m for c in scale(x, b))


def literal_extension(s, u, v, w, modulus):
    total = (0, 0)
    for xu, xv, xw in product(range(2), repeat=3):
        # Actual signed ternary clause: not u or not v or L_s(w).
        if xu and xv and xw != s:
            continue
        factor = (1, 0)
        for assignment, value in zip((xu, xv, xw), (u, v, w)):
            z = value if assignment else qadd((1, 0), qscale(value, -1, modulus), modulus)
            factor = qmul(factor, z, modulus)
        total = qadd(total, factor, modulus)
    return total


@cache
def escape_rows(a, t, z, precision, minimal=False):
    L = 1 << a
    i = order2(t)
    B = 2 << i
    modulus = 1 << precision
    marks = ([0], [L - 1], []) if minimal else (range(B), range(L - B, L), [])
    tables = []
    for x in range(L):
        args = []
        for ys in marks:
            arg = (0, 0)
            for y in ys:
                if bit(x, i) != bit(y, i):
                    arg = qadd(arg, pair_mod(kernel(a, t, z, y - x), modulus), modulus)
            args.append(arg)
        alternatives = []
        for s in (0, 1):
            value = literal_extension(s, *args, modulus)
            d1 = literal_extension(s, (1, 0), args[1], args[2], modulus)
            d0 = literal_extension(s, (0, 0), args[1], args[2], modulus)
            derivative = qadd(d1, qscale(d0, -1, modulus), modulus)
            alternatives.append((value, derivative))
        tables.append((args, alternatives))
    return tables


def actual_singletons(a, t, z, word, precision, minimal=False):
    """Sum each actual old row table, then extract the single target mode.

    Original column pins give a unique assignment. A single source tile
    has moment 1 (or 0 for unmarked tiles of the four-slot direct test).
    """
    L = 1 << a
    i = order2(t)
    B = 2 << i
    modulus = 1 << precision
    rows = escape_rows(a, t, z, precision, minimal)
    vals = [table[bit(word, x)] for x, (_, table) in enumerate(rows)]
    prefix = [(1, 0)]
    suffix = [(1, 0)] * (L + 1)
    for value, _ in vals:
        prefix.append(qmul(prefix[-1], value, modulus))
    for x in reversed(range(L)):
        suffix[x] = qmul(suffix[x + 1], vals[x][0], modulus)
    result = []
    for tile in range(B):
        total = (0, 0)
        for x in range(L):
            if bit(x, i) != bit(tile, i):
                continue
            coef = pair_mod(crossing(a, t, z, x, tile, 0), modulus)
            term = qmul(prefix[x], qmul(coef, vals[x][1], modulus), modulus)
            total = qadd(total, qmul(term, suffix[x + 1], modulus), modulus)
        result.append((0, 0) if minimal and tile != 0 else total)
    return result


def direct_child_test():
    """Independent source-style Y enumeration inside both nonempty children."""
    tested = 0
    a, t, i, L, p = 2, 1, 0, 4, 7
    m = 1 << p
    for z in ((0, 0), (1, 0), (0, 1), (1, 1), (2, 0)):
        rows = escape_rows(a, t, z, p, True)
        for word in range(1 << L):
            assembled = (1, 0)
            for g in (0, 1):
                xs = [x for x in range(L) if bit(x, i) == g]
                child = (0, 0)
                for assignment in product(range(2), repeat=3 * len(xs)):
                    constant, linear = (1, 0), (0, 0)
                    for j, x in enumerate(xs):
                        yy = assignment[3 * j:3 * j + 3]
                        if yy[0] and yy[1] and yy[2] != bit(word, x):
                            constant, linear = (0, 0), (0, 0)
                            break
                        for port, (yb, arg) in enumerate(zip(yy, rows[x][0])):
                            sign = 2 * yb - 1
                            local = qadd((1 - yb, 0), qscale(arg, sign, m), m)
                            term = (0, 0)
                            if port == 0 and g == 0:
                                raw = pair_mod(crossing(a, t, z, x, 0, 0), m)
                                term = qscale(raw, sign, m)
                            linear = qadd(qmul(linear, local, m), qmul(constant, term, m), m)
                            constant = qmul(constant, local, m)
                    child = qadd(child, linear if g == 0 else constant, m)
                # The source's tile moment is exactly 1, since only U[0] is 1.
                assembled = qmul(assembled, child, m)
            assert assembled == actual_singletons(a, t, z, word, p, True)[0]
            expected = qscale(z, bit(word, 2) * (1 << 3), 1 << 4)
            assert tuple(v % (1 << 4) for v in assembled) == expected
            tested += 1
    return tested


def check_escape():
    a = 4
    L = 1 << a
    summary = []
    for i in (0, 1):
        B = 2 << i
        delta = a + 1 - i
        ts = [t for t in range(B, L - B + 1) if order2(t) == i]
        addresses = [(t, tile, next(x for x in range(L - B - t, L - t) if x % B == tile))
                     for t in ts for tile in range(B)]
        xs = sorted(x for _, _, x in addresses)
        assert len(set(xs)) == len(xs) == L - 2 * B
        if i == 1:
            words = [sum(bit(n, j) << x for j, x in enumerate(xs)) for n in range(1 << len(xs))]
        else:
            rng = Random(20261126)
            words = [0, (1 << L) - 1] + [1 << x for x in range(L)]
            words.extend(rng.randrange(1 << L) for _ in range(24))
        menus = set()
        checks = 0
        for j, word in enumerate(words):
            for z in ([(0, 1)] if j >= 5 else [(0, 1), (1, 1), (1, 0), (0, 0), (2, 0)]):
                slots = {t: actual_singletons(a, t, z, word, delta + 1) for t in ts}
                obs = []
                for t, tile, x in addresses:
                    actual = slots[t][tile]
                    expected = qscale(z, (1 << delta) * bit(word, x), 1 << (delta + 1))
                    assert actual == expected
                    obs.append(actual)
                    checks += 1
                if z == (0, 1):
                    menus.add(tuple(obs))
        if i == 1:
            assert len(menus) == 1 << len(xs)
        summary.append(dict(i=i, eligible_nodes=ts, address_bits=len(xs),
                            tested_words=len(words), distinct_tested_menus=len(menus),
                            complete_slot_checks=checks))
    return dict(block_gadgets=summary, direct_original_child_contractions=direct_child_test())


def poly_product(a, b, n, modulus=None):
    out = [0] * (n + 1)
    for i, v in enumerate(a):
        for j, w in enumerate(b[:n - i + 1]):
            out[i + j] += v * w
    return [v % modulus for v in out] if modulus is not None else out


@cache
def raw_series(a, t, x, y, b, n, modulus):
    """Ordinary z coefficients from the uncancelled rational source product.

    Set b=-1 for a local entry, and b>=0 for the specified crossing mode.
    """
    L = 1 << a
    q = y - x
    coefs = [1] + [0] * n
    for d in range(-L, L):
        if d != q:
            coefs = poly_product(coefs, [t - d, 2 * L], n)
    origin_denominator = prod(-d for d in range(-L, L) if d)
    coefs = [Fraction(c, origin_denominator) for c in coefs]
    if b > 0:
        d = t - q
        geometric = [Fraction((2 << order2(t)) * (-2 * L) ** j, d ** (j + 1))
                     for j in range(n + 1)]
        for _ in range(b):
            coefs = poly_product(coefs, geometric, n)
    return [residue(c, modulus) for c in coefs]


def equality_fixture(t, modes, tables, n=5, p=23):
    """Literal complete-slot sum for four four-slot packets with equality columns."""
    a, i, L = 2, order2(t), 4
    B = 2 << i
    delta = a + 1 - i
    number_packets = 4
    m = 1 << p
    exponents = tuple(exponent for _, _, _, exponent in modes)
    zero = (0,) * len(modes)
    cost = sum((delta + b) * e for _, _, b, e in modes)
    count = sum(exponents)
    scalar = [0] * (n + 1)
    for assignment in range(1 << 8):
        def column(packet, y):
            return bit(assignment, (packet // 2) * L + y)

        source = prod(sum((y // B) ** b * column(packet, y)
                          for y in range(tile, L, B)) ** exponent
                      for packet, tile, b, exponent in modes)
        if not source:
            continue
        states = {zero: [source] + [0] * n}
        for packet in range(number_packets):
            for x in range(L):
                left, right = tables[packet * L + x]
                slope = right - left
                local = [left] + [0] * n
                for y in range(L):
                    if bit(y, i) != bit(x, i) and column(packet, y):
                        ker = raw_series(a, t, x, y, -1, n, m)
                        local = [(v + slope * w) % m for v, w in zip(local, ker)]
                options = [(None, local)]
                for j, (target_packet, tile, b, _) in enumerate(modes):
                    if target_packet == packet and bit(tile, i) == bit(x, i):
                        ker = raw_series(a, t, x, tile, b, n, m)
                        options.append((j, [(slope * v) % m for v in ker]))
                new = {}
                for state, pol in states.items():
                    for index, multiplier in options:
                        updated = state
                        if index is not None:
                            if state[index] >= exponents[index]:
                                continue
                            updated = tuple(v + (j == index) for j, v in enumerate(state))
                        term = poly_product(pol, multiplier, n, m)
                        prev = new.get(updated, [0] * (n + 1))
                        new[updated] = [(v + w) % m for v, w in zip(prev, term)]
                states = new
        scalar = [(v + w) % m for v, w in zip(scalar, states.get(exponents, [0] * (n + 1)))]

    supported = {(packet // 2) * L + (x + t) for packet in range(number_packets)
                 for x in range(L) if 0 <= x + t < L}
    K = 8 - len(supported)
    nontrivial = 0
    for j, value in enumerate(scalar):
        if j < count:
            assert value == 0
            continue
        order = cost + max(j - count, K - count)
        assert value % (1 << min(order, p)) == 0
        nontrivial += int(value != 0)
    return K, nontrivial


def check_equality_coefficients():
    # A constant row table occasionally leaves a genuine free column bit alive.
    # Alternating pins and all permissive tables produce different parities.
    patterns = [
        [(1, 1) if x % 4 in (0, 3) else (1, 0) for x in range(16)],
        [(1, 0) if x % 3 == 0 else (1, 1) for x in range(16)],
    ]
    modes = [[], [(0, 0, 0, 1)], [(1, 1, 1, 1)], [(0, 0, 0, 2)],
             [(0, 0, 0, 1), (2, 0, 0, 1)]]
    total = nonzero = 0
    counts = {}
    for pattern in patterns:
        for t in (-3, -1, 1, 3):
            for beta in modes:
                K, n = equality_fixture(t, beta, pattern)
                counts[t] = K
                nonzero += n
                total += 6
    assert nonzero > 0
    return dict(coefficient_checks=total, nonzero_coefficients=nonzero,
                unsupported_equality_counts=counts)


def physical_packing_test():
    # Reuse the immutable v8 physical CNF builder without writing a pycache there.
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "research_v8" / "checks"))
    from common_family_counts import cubic_completion, shortened_cnf

    order, graph = cubic_completion(16)
    clauses = shortened_cnf(order, graph, 0)
    a, r, L = 2, 2, 4
    rng = Random(73951)
    labels = list(product(range(r), repeat=a))
    var_labels = {abs(v): rng.choice(labels) for clause in clauses for v in clause}
    clause_labels = [rng.choice(labels) for _ in clauses]
    guards = []
    cells = Counter()
    for clause_no, clause in enumerate(clauses):
        for v in clause:
            eq = rng.choice(labels)
            pair = ((clause_labels[clause_no], eq), (var_labels[abs(v)], eq))
            guards.append(pair)
            cells.update(pair)
    M = 2 * len(guards)
    assert M == 30 * order + 4
    Hpad = ((max(cells.values()) + L - 1) // L) * L
    b = Hpad // L
    by_cell = defaultdict(list)
    n_packets = 0
    unordered = list(combinations_with_replacement(range(r), 2))
    for pairs in product(unordered, repeat=a):
        unequal = [j for j, pair in enumerate(pairs) if pair[0] != pair[1]]
        for _ in range(b):
            for mask in range(1 << len(unequal)):
                flips = {j: bit(mask, h) for h, j in enumerate(unequal)}
                for y in range(L):
                    rot = [bit(y, j) ^ flips.get(j, 0) for j in range(a)]
                    row = tuple(pair[rot[j]] for j, pair in enumerate(pairs))
                    col = tuple(pair[1 - rot[j]] for j, pair in enumerate(pairs))
                    by_cell[row, col].append((n_packets, y))
                n_packets += 1
    for cell, slots in by_cell.items():
        assert len(slots) == Hpad
        assert sum(y == 0 for _, y in slots) == sum(y == L - 1 for _, y in slots) == b
        assert cells[cell] <= Hpad

    # Conditional quadratic means, scaled by L to use only integers.
    total_devs = [0, 0]
    local_devs = [Counter(), Counter()]
    marks = []
    for guard in guards:
        inc = Counter(guard)

        def increment(color):
            penalty = 0
            for sign in range(2):
                d = L * (color == sign) - 1
                penalty += 2 * total_devs[sign] * d + d * d
                for cell, weight in inc.items():
                    z = weight * d
                    penalty += 2 * local_devs[sign][cell] * z + z * z
            return penalty

        color = min((2, 0, 1), key=increment)
        marks.append(color)
        for sign in range(2):
            d = L * (color == sign) - 1
            total_devs[sign] += d
            for cell, weight in inc.items():
                local_devs[sign][cell] += weight * d
    before_trim = [marks.count(sign) for sign in range(2)]
    for sign in range(2):
        loads = Counter(cell for j, guard in enumerate(guards) if marks[j] == sign for cell in guard)
        for j, guard in enumerate(guards):
            if marks[j] == sign and any(loads[cell] > b for cell in guard):
                marks[j] = 2
                loads.subtract(guard)
        assert max(loads.values()) <= b

    fixed = {}
    for j, guard in enumerate(guards):
        if marks[j] == 2:
            continue
        y = (L - 1) * marks[j]
        for port, cell in enumerate(guard):
            slots = by_cell[cell]
            k = next(k for k, slot in enumerate(slots) if slot[1] == y)
            fixed[j, port] = slots.pop(k)
    for j, guard in enumerate(guards):
        for port, cell in enumerate(guard):
            if (j, port) not in fixed:
                fixed[j, port] = by_cell[cell].pop()
    real = set(fixed.values())
    assert len(real) == M
    result = {}
    for t in range(-L + 1, L):
        if not t:
            continue
        occupied = []
        for j, guard in enumerate(guards):
            positions = [fixed[j, h] for h in range(len(guard))]
            no_match = all((p, y - t) not in real for p, y in positions)
            if marks[j] == (0 if t > 0 else 1):
                assert no_match
            occupied.append(no_match)
        result[t] = sum(occupied)

    # On the same original physical incidences, sample independent masks
    # per unordered type and uniform positions in every ordered cell.
    real_by_cell = defaultdict(list)
    for j, guard in enumerate(guards):
        for h, cell in enumerate(guard):
            real_by_cell[cell].append(2 * j + h)
    expected = Fraction(0)
    for cell_a, cell_b in guards:
        if cell_a != cell_b:
            # Given their common column label, distinct cells are distinct types.
            expected += Fraction(1, L * L)
        else:
            unequal_count = sum(x != y for x, y in zip(*cell_a))
            orientations = 1 << unequal_count
            endpoints = b * orientations
            expected += Fraction(endpoints * (endpoints - 1),
                                 orientations * Hpad * (Hpad - 1))
    assert expected >= (1 - Fraction(1, b)) * Fraction(M, 2 * L * L)
    observations = [[], []]
    for _ in range(64):
        quotas = defaultdict(lambda: [0, 0])
        for pairs in product(unordered, repeat=a):
            unequal = [j for j, pair in enumerate(pairs) if pair[0] != pair[1]]
            mask = rng.randrange(1 << len(unequal))
            flips = {j: bit(mask, h) for h, j in enumerate(unequal)}
            for sign in range(2):
                choices = [sign ^ flips.get(j, 0) for j in range(a)]
                row = tuple(pair[choices[j]] for j, pair in enumerate(pairs))
                col = tuple(pair[1 - choices[j]] for j, pair in enumerate(pairs))
                quotas[row, col][sign] = b * (1 << len(unequal))
        endpoint_ports = [set(), set()]
        for cell, ports in real_by_cell.items():
            order_with_padding = list(ports) + [-1] * (Hpad - len(ports))
            rng.shuffle(order_with_padding)
            qplus, qminus = quotas[cell]
            endpoint_ports[0].update(order_with_padding[:qplus])
            if qminus:
                endpoint_ports[1].update(order_with_padding[-qminus:])
        for sign, chosen in enumerate(endpoint_ports):
            observations[sign].append(sum(2 * j in chosen and 2 * j + 1 in chosen
                                          for j in range(len(guards))))
    return dict(cubic_vertices=order, wires=M, padded_load=Hpad, packets=n_packets,
                endpoint_quota_per_cell=b, colors_before_trimming=before_trim,
                retained_positive_negative=[marks.count(0), marks.count(1)],
                actual_unsupported_equalities=result,
                random_order_expected_per_sign=str(expected),
                random_order_trials=len(observations[0]),
                random_order_mean_by_sign=[str(Fraction(sum(x), len(x))) for x in observations])


def check_generating_function():
    counts = 0
    for p in range(1, 11):
        for delta in (2, 3):
            costs = [delta, delta, delta + 1, delta + 1, delta + 2]
            coefficients = [1] + [0] * (p - 1)
            for c in costs:
                for s in range(c, p):
                    coefficients[s] += coefficients[s - c]
            h = sum(n * comb(p - w + 1, 2) for w, n in enumerate(coefficients))
            direct = 0
            for beta in product(*(range((p - 1) // c + 1) for c in costs)):
                w = sum(c * b for c, b in zip(costs, beta))
                if w < p:
                    direct += sum(p - w - j for j in range(p - w))
            assert h == direct
            counts += 1
    return counts


def check_printed_address_subset():
    inspected = 0
    for u in (3, 5, 8, 16):
        a = 2 * u
        L = 1 << a
        M = 1 << (40 * u)
        for i in range(u):
            D = L >> i
            tiles = 2 * (M // D) * 63 // 64
            d = isqrt(D * D // (16 * u))
            v = tiles * (d * (a + 1 - i) + d * (d - 1) // 2)
            source_precision_lower_bound = 24 * M * D // u
            assert 1 <= d <= D // 2
            assert v + M < source_precision_lower_bound
            inspected += 1
    return inspected


if __name__ == "__main__":
    print(json.dumps(dict(raw_crossings=check_crossings(), first_extra_digit=check_escape(),
                          equality_series=check_equality_coefficients(),
                          physical_packing=physical_packing_test(),
                          generating_functions=check_generating_function(),
                          printed_address_subset_parameters=check_printed_address_subset()), indent=2))
