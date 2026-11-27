"""Exact small-instance checks of the exceptional measurement projection."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb


def row_rank(rows):
    basis = {}
    for source in rows:
        row = list(map(Fraction, source))
        for pivot in sorted(basis):
            coefficient = row[pivot]
            if coefficient:
                row = [x - coefficient * y for x, y in zip(row, basis[pivot])]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is not None:
            basis[pivot] = [x / row[pivot] for x in row]
    return len(basis)


def image_size(rows, n):
    rows = sorted(set(tuple(row) for row in rows if any(row)))
    sums = {(0,) * len(rows)}
    for variable in range(n):
        column = tuple(row[variable] for row in rows)
        sums |= {tuple(x + y for x, y in zip(value, column)) for value in sums}
    return len(sums)


def sample_layout(r, q, repeat_cells):
    words = list(product(range(r), repeat=q))
    variables = []
    for i, word in enumerate(words):
        if repeat_cells:
            # The second occurrence of an identical cell goes to a new copy.
            for j in range(2):
                variables.append((word, [words[2*j], words[2*j], words[2*j+1]]))
        else:
            degree = (len(words) + 1) // 2
            variables.append((word, [words[(i+j) % len(words)] for j in range(degree)]))
    load = Counter()
    slots = []
    for variable, (first, seconds) in enumerate(variables):
        for second in seconds:
            copy = load[first, second]
            load[first, second] += 1
            slots.append((variable, copy, first, second))
    assert max(load.values()) * len(words)**2 <= 2 * len(slots)
    return variables, slots


def check(r, q, variables, slots, retained):
    n = len(variables)
    degrees = [len(seconds) for _, seconds in variables]
    rows = {}
    diagonal_sum = Fraction()
    for variable, copy, first, second in slots:
        orbit = tuple(tuple(sorted((a, d))) for a, d in zip(first, second))
        unequal = [i for i in range(q) if first[i] != second[i]]
        k = len(unequal)
        outside = sum(comb(k, j) for j in range(k+1) if j not in retained)
        diagonal_sum += Fraction(outside, (1 << k) * degrees[variable])
        backwards = sum((first[i] > second[i]) << j for j, i in enumerate(unequal))
        for anti in range(1 << k):
            if anti.bit_count() not in retained:
                row = rows.setdefault((copy, orbit, anti, k), [0] * n)
                row[variable] += (-1)**((anti & backwards).bit_count())
    computed_sum = sum(
        Fraction(value**2, (1 << key[3]) * degrees[variable])
        for key, row in rows.items()
        for variable, value in enumerate(row)
    )
    assert computed_sum == diagonal_sum
    rank = row_rank(rows.values())
    assert diagonal_sum <= rank
    node_ranks = []
    for t in range(q):
        split = [
            [value if variables[v][0][t] == g else 0 for v, value in enumerate(row)]
            for row in rows.values() for g in range(r)
        ]
        local_rank = row_rank(split)
        assert rank <= local_rank
        assert image_size(split, n) >= 2**local_rank
        node_ranks.append(local_rank)
    return diagonal_sum, rank, node_ranks


def main():
    cases = [(2, 2, True), (2, 3, False), (3, 2, False)]
    for r, q, repeats in cases:
        variables, slots = sample_layout(r, q, repeats)
        tested = []
        for length in range(1, q):
            for start in range(q + 2 - length):
                retained = range(start, start + length)
                tested.append(check(r, q, variables, slots, retained))
        ranks = [rank for _, rank, _ in tested]
        node_ranks = [rank for _, _, node in tested for rank in node]
        print(
            f"r={r}, Q={q}, n={len(variables)}, M={len(slots)}, "
            f"intervals={len(tested)}, nodes={len(node_ranks)}, "
            f"global rank={min(ranks)}..{max(ranks)}, "
            f"node rank={min(node_ranks)}..{max(node_ranks)}"
        )


if __name__ == "__main__":
    main()
