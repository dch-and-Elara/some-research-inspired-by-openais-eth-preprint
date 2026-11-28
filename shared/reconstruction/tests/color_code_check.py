"""Exact, dependency-free checks of the central cyclic-color codes."""
from fractions import Fraction
from itertools import combinations, product
from math import prod


def unit(n, i):
    return tuple(int(j == i) for j in range(n))


def basis(rows):
    """Rational echelon dictionary, indexed by the pivot."""
    echelon = {}
    for input_row in rows:
        row = list(map(Fraction, input_row))
        for pivot, pivot_row in sorted(echelon.items()):
            coefficient = row[pivot]
            if coefficient:
                row = [x - coefficient * y for x, y in zip(row, pivot_row)]
        pivot = next((j for j, value in enumerate(row) if value), None)
        if pivot is not None:
            lead = row[pivot]
            echelon[pivot] = [x / lead for x in row]
    return echelon


def member(row, echelon):
    row = list(map(Fraction, row))
    for pivot, v in sorted(echelon.items()):
        if row[pivot]:
            coefficient = row[pivot]
            row = [x - coefficient * y for x, y in zip(row, v)]
    return not any(row)


def matchings(r):
    size = r if r % 2 == 0 else r + 1
    group = size - 1
    output = []
    for j in range(group):
        edges = [(group, j)]
        edges.extend(((j + i) % group, (j - i) % group)
                     for i in range(1, (size - 2) // 2 + 1))
        output.append([tuple(sorted((a, b))) for a, b in edges if max(a, b) < r])
    assert sorted(e for matching in output for e in matching) == list(combinations(range(r), 2))
    return output


def colored_basis(r):
    n = r * r
    match = matchings(r)
    k = len(match)
    p = 2 * k + 1
    rows = []
    for b in range(r):
        rows.append((0, tuple(int(i % r == b) for i in range(n))))
    for matching, start in zip(match, range(-k + 1, 1)):
        for a, b in matching:
            x = unit(n, a * r + b)
            y = unit(n, b * r + a)
            for color, sign in ((start - 1, 1), (start + k, -1)):
                rows.append((color % p, tuple(u + sign * v for u, v in zip(x, y))))
    assert len(basis(row for _, row in rows)) == n
    return p, k, rows


def cyclic_interval(start, k, p):
    return {(start + j) % p for j in range(k)}


def local_tests(r):
    p, k, rows = colored_basis(r)
    checked = 0
    for start in range(p):
        allowed = cyclic_interval(start, k, p)
        enc = [row for color, row in rows if color in allowed]
        for b in range(r):
            unknown = [i for i in range(r * r) if i // r != b]
            echelon = basis(tuple(row[i] for i in unknown) for row in enc)
            for a in range(r):
                assert member(tuple(int(i == a * r + b) for i in unknown), echelon)
                checked += 1
    return checked


def full_tests(q, r):
    p, k, rows = colored_basis(r)
    sequences = list(product(range(r * r), repeat=q))
    allowed = cyclic_interval(1, k, p)
    enc = []
    for choice in product(rows, repeat=q):
        if sum(c for c, _ in choice) % p in allowed:
            enc.append(tuple(prod(x[i] for (_, x), i in zip(choice, word)) for word in sequences))
    m = r // 2
    expected = k * (r ** (2 * q) - (r - m) ** q) // p
    assert len(basis(enc)) == len(enc) == expected
    assert all(abs(value) <= 1 for row in enc for value in row)
    checked = 0
    for t in range(q):
        for b in range(r):
            unknown = [j for j, word in enumerate(sequences) if word[t] // r != b]
            echelon = basis([row[j] for j in unknown] for row in enc)
            for j, word in enumerate(sequences):
                if word[t] % r == b:
                    assert member(tuple(int(j == i) for i in unknown), echelon)
                    checked += 1
    return len(enc), checked


def convolution_tests(r):
    p, k, rows = colored_basis(r)
    first = [sum(c == j for c, _ in rows) for j in range(p)]
    counts = [1] + [0] * (p - 1)
    checked = 0
    for q in range(1, 14):
        counts = [sum(counts[j] * first[(i - j) % p] for j in range(p)) for i in range(p)]
        m = r // 2
        expected = (r ** (2 * q) - (r - m) ** q) // p
        assert counts == [expected + (r - m) ** q] + [expected] * (p - 1)
        if r == 2:
            assert expected == (4 ** q - 1) // 3
        checked += p
    return checked


def converse_tests():
    count = 0
    for r in range(2, 6):
        for q in range(1, 5):
            words = list(product(range(r), repeat=q))
            earliest = [min((c, t) for t, c in enumerate(word)) for word in words]
            selected = sum(i < j for i in earliest for j in earliest)
            geometric = sum(Fraction(j - 1, 2 * j - 1)
                            * (j ** (2 * q) - (j - 1) ** (2 * q))
                            for j in range(2, r + 1))
            telescoped = (Fraction(r - 1, 2 * r - 1) * r ** (2 * q)
                          - sum(Fraction(j ** (2 * q), 4 * j * j - 1)
                                for j in range(1, r)))
            assert selected == geometric == telescoped, (q, r)
            count += 1
    return count


if __name__ == '__main__':
    print(f'receiver-order converse: {converse_tests()} fully enumerated arrays')
    local = 0
    conv = 0
    for r in range(2, 9):
        local += local_tests(r)
        conv += convolution_tests(r)
    print(f'one-slot rational membership: {local} tests (r = 2,...,8)')
    print(f'cyclic coefficient counts: {conv} tests (q = 1,...,13)')
    global_count = 0
    for r, q in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 1)):
        rank, checks = full_tests(q, r)
        global_count += checks
        print(f'full physical matrix r={r} q={q}: rank={rank}, direct demands={checks}')
    print(f'full rational membership: {global_count} receiver/demand checks')
