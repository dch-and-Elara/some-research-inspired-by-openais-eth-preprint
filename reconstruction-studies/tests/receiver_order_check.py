"""Compare the hypercuboid receiver-order formula with two exact optimizations."""
from functools import cache
from fractions import Fraction
from itertools import permutations, product
from math import prod


def closed_form(sizes):
    def volume(level):
        return prod(min(size, level) ** 2 for size in sizes)

    return sum(
        Fraction(level - 1, 2 * level - 1) * (volume(level) - volume(level - 1))
        for level in range(2, max(sizes) + 1)
    )


@cache
def optimal_from_state(sizes):
    if 0 in sizes:
        return 0
    scores = []
    for coordinate, size in enumerate(sizes):
        remaining = list(sizes)
        remaining[coordinate] -= 1
        contributions = prod(
            n * n for index, n in enumerate(sizes) if index != coordinate
        )
        scores.append((size - 1) * contributions + optimal_from_state(tuple(remaining)))
    return max(scores)


def brute_force(sizes):
    nodes = [(t, c) for t, r in enumerate(sizes) for c in range(r)]
    transversals = list(product(*(range(r) for r in sizes)))
    best = count = 0
    for order in permutations(nodes):
        rank = {node: i for i, node in enumerate(order)}
        # The holder and requested-word transversals range over the same list.
        earliest = [min(rank[t, c] for t, c in enumerate(word)) for word in transversals]
        score = sum(first_demand < first_hold for first_demand in earliest for first_hold in earliest)
        best = max(best, score)
        count += 1
    return best, count


def main():
    profiles = [sizes for q in range(1, 5) for sizes in product(range(1, 5), repeat=q)]
    for sizes in profiles:
        assert optimal_from_state(sizes) == closed_form(sizes)
    print(f"State-space optima equal the closed form on all {len(profiles)} ordered profiles (1..4 slots, sizes 1..4).")
    total_orders = 0
    for sizes in [(1,), (3,), (2, 2), (2, 3), (2, 2, 2), (1, 4, 2), (2, 2, 3)]:
        optimum, count = brute_force(sizes)
        assert optimum == closed_form(sizes)
        print(f"{sizes}: direct maximum {optimum} / {prod(sizes)**2} on {count} labeled receiver orders.")
        total_orders += count
    print(f"All {total_orders} direct receiver permutations checked.")


if __name__ == "__main__":
    main()
