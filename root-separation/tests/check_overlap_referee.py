"""Independent finite checks for the overlap referee report, using only integers."""

from collections import deque
from itertools import combinations, product
from math import prod


def mixed_domain_control():
    # Cui et al., Example 3.15, with two binary-output adapters and one unused input.
    left = {"a0", "a1", "a2", "a3"}
    right = {"b0", "b1", "b2", "b3"}
    variables = sorted(left | right | {"z", "w", "s", "t"})
    scopes = [("a1", "z", "w"), ("a0", "z", "s"), ("a2", "w", "t"),
              ("s", "b0", "b1"), ("t", "b2", "b3")]
    neighbors = {v: set() for v in variables}
    for scope in scopes:
        for x, y in combinations(scope, 2):
            neighbors[x].add(y)
            neighbors[y].add(x)

    best = None
    for choice in product([False, True], repeat=len(variables)):
        cut = {v for v, removed in zip(variables, choice) if removed}
        seen = left - cut
        queue = deque(seen)
        while queue:
            v = queue.popleft()
            new = neighbors[v] - cut - seen
            seen.update(new)
            queue.extend(new)
        if seen.isdisjoint(right):
            cost = prod(3 if v in {"s", "t"} else 2 for v in cut)
            if best is None or cost < best:
                best = cost
    assert best == 8

    bitstrings = list(product(range(2), repeat=4))
    rows = []
    for a in bitstrings:
        row = []
        for b in bitstrings:
            value = sum(z == w == a[1] and s == a[0] + z and t == a[2] + w
                        and s == b[0] + 2 * b[1] and t == b[2] + 2 * b[3]
                        for z, w, s, t in product(range(2), range(2), range(3), range(3)))
            row.append(value)
        assert sum(row) == 1
        rows.append(tuple(row))
    # Distinct standard basis rows are independent over every field.
    assert len(set(rows)) == 7
    print(f"Mixed domains: {2**len(variables)} cuts, separator capacity {best}, explicit matrix rank 7.")


def quadratic_multiply(x, y):
    # Integer coordinates in Z[u]/(u^2 + u + 1).
    a, b = x
    c, d = y
    return a*c - b*d, a*d + b*c - b*d


def valuation(x, precision):
    def coordinate(v):
        if v == 0:
            return precision
        return min(precision, (v & -v).bit_length() - 1)
    return min(map(coordinate, x))


def kernel_entry(length, center, lift, x, y, precision):
    grid = range(-length, length)
    t = center + 2 * length * lift[0], 2 * length * lift[1]
    numerator = (1, 0)
    for q in grid:
        if q != y - x:
            numerator = quadratic_multiply(numerator, (t[0] - q, t[1]))
    denominator = prod(-q for q in grid if q)
    power_of_two = abs(denominator) & -abs(denominator)
    odd_part = denominator // power_of_two
    assert all(v % power_of_two == 0 for v in numerator)
    modulus = 2**precision
    return tuple((v // power_of_two) * pow(odd_part, -1, modulus) % modulus
                 for v in numerator)


def odd_grid_control():
    precision = 13
    modulus = 2**precision
    unit_lifts = [v for v in product(range(4), repeat=2) if any(c % 2 for c in v)]
    unit_checks = zero_checks = 0
    for length in (2, 4, 8):
        expected_valuation = length.bit_length()
        for center in range(-length + 1, length, 2):
            for x, y in product(range(length), repeat=2):
                if x % 2 != y % 2:
                    continue
                zero_lift = kernel_entry(length, center, (0, 0), x, y, precision)
                assert zero_lift == (0, 0)
                zero_checks += 1
                for lift in unit_lifts:
                    weight = kernel_entry(length, center, lift, x, y, precision)
                    assert valuation(weight, precision) == expected_valuation
                    running = (1, 0)
                    cutoff = (precision + expected_valuation - 1) // expected_valuation
                    for k in range(1, cutoff + 1):
                        running = tuple(c % modulus for c in quadratic_multiply(running, weight))
                        assert valuation(running, precision) == min(k * expected_valuation, precision)
                    assert running == (0, 0)
                    unit_checks += 1
    assert (unit_checks, zero_checks) == (3504, 292)
    print(f"Quadratic extension: {unit_checks} unit coefficients with truncation thresholds; "
          f"{zero_checks} zero-lift coefficients.")


def fingerprint_control():
    labels = [x for x in range(16) if x.bit_count() == 2]
    distinct = [(x, y) for x in labels for y in labels if x != y]
    for x, y in distinct:
        collision_count = sum(((seed & (x ^ y)).bit_count() % 2) == 0
                              for seed in range(16))
        assert collision_count == 8
    print(f"Public equality fingerprints: all {len(distinct)} ordered unequal labels "
          "collide on 8 of the 16 seeds.")


if __name__ == "__main__":
    mixed_domain_control()
    odd_grid_control()
    fingerprint_control()
