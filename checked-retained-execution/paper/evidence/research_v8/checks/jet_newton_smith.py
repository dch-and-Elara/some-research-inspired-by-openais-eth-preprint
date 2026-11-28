"""Compare weighted Newton columns and raw jet-polynomial evaluations over Z/r^P."""

import json
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
from math import factorial, prod


def compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for head in range(total + 1):
        for tail in compositions(total - head, slots - 1):
            yield (head,) + tail


def valuation(number, prime, precision):
    order = 0
    while order < precision and number % prime == 0:
        number //= prime
        order += 1
    return order


def smith_orders(matrix, prime, precision):
    """Eliminate minimum-valuation pivots over the local principal ideal ring."""
    modulus = prime**precision
    rows = [[entry % modulus for entry in row] for row in matrix]
    orders = []
    while rows and rows[0]:
        pivot = min(
            ((valuation(value, prime, precision), i, j)
             for i, row in enumerate(rows) for j, value in enumerate(row) if value),
            default=None,
        )
        if pivot is None:
            break
        order, i, j = pivot
        scale = prime**order
        pivot_row = rows.pop(i)
        unit_inverse = pow(pivot_row[j] // scale, -1, modulus)
        pivot_row = [value * unit_inverse % modulus for value in pivot_row]
        for i, row in enumerate(rows):
            factor = row[j] // scale
            rows[i] = [(value - factor * pivot_value) % modulus
                       for index, (value, pivot_value) in enumerate(zip(row, pivot_row))
                       if index != j]
        # Clearing the rest of the pivot row now leaves this submatrix unchanged.
        orders.append(order)
    return orders


@lru_cache(None)
def stirling(n, j):
    if j > n or j < 0:
        return 0
    if n == 0:
        return int(j == 0)
    if j == 0:
        return 0
    return j * stirling(n - 1, j) + stirling(n - 1, j - 1)


def taylor_features(prime, precision, length, messages):
    degree = precision + length - 2
    for total in range(degree + 1):
        for alpha in compositions(total, messages):
            features = [dict() for _ in range(length)]
            for blocks in product(*(compositions(a, length) for a in alpha)):
                jet_degree = sum(r * count for block in blocks
                                 for r, count in enumerate(block))
                if jet_degree >= length:
                    continue
                powers = tuple(x for block in blocks for x in block)
                zero_powers = sum(block[0] for block in blocks)
                coefficient = prime**zero_powers * prod(
                    factorial(a) // prod(factorial(b) for b in block)
                    for a, block in zip(alpha, blocks)
                )
                features[jet_degree][powers] = coefficient
            for feature in features:
                least = min((valuation(c, prime, precision) for c in feature.values()),
                            default=precision)
                if least < precision:
                    yield least, feature


def weighted_profile(prime, precision, length, messages):
    features = list(taylor_features(prime, precision, length, messages))
    rows = defaultdict(lambda: [0] * len(features))
    for column, (_, terms) in enumerate(features):
        for exponents, coefficient in terms.items():
            # x^b = sum_j S(b,j)(x)_j. Replacing (x)_j by binom(x,j)
            # supplies j!, which differs from the theoretical weight by a unit.
            choices = [range(1, exponent + 1) if exponent else (0,)
                       for exponent in exponents]
            for indices in product(*choices):
                multiplier = prod(stirling(b, j) * factorial(j)
                                  for b, j in zip(exponents, indices))
                rows[indices][column] += coefficient * multiplier
    profile = smith_orders(list(rows.values()), prime, precision)
    coefficient_weights = sorted(weight for weight, _ in features)
    return profile, coefficient_weights


def multiply_jets(left, right, modulus):
    return tuple(sum(left[a] * right[j - a] for a in range(j + 1)) % modulus
                 for j in range(len(left)))


def raw_profile(prime, precision, length, messages):
    modulus = prime**precision
    one = (1,) + (0,) * (length - 1)
    degree_bound = prime * (precision + length - 1)
    jets = list(product(range(modulus), repeat=length))
    powers = {}
    for jet in jets:
        current = one
        entries = []
        for _ in range(degree_bound):
            entries.append(current)
            current = multiply_jets(current, jet, modulus)
        powers[jet] = entries
    matrix = []
    for inputs in product(jets, repeat=messages):
        row = []
        for factors in product(*(powers[jet] for jet in inputs)):
            value = one
            for factor in factors:
                value = multiply_jets(value, factor, modulus)
            row.extend(value)
        matrix.append(row)
    return smith_orders(matrix, prime, precision), (len(matrix), len(matrix[0]))


def histogram(values):
    return dict(sorted(Counter(values).items()))


def check(cases):
    results = []
    for prime, length, messages, loss, output_precision in cases:
        precision = loss + output_precision
        predicted, coefficient_weights = weighted_profile(prime, precision, length, messages)
        measured, shape = raw_profile(prime, precision, length, messages)
        fibers = prime**messages
        assert sorted(predicted * fibers) == sorted(measured)
        results.append({
            "residue_size": prime,
            "jet_length": length,
            "messages": messages,
            "loss": loss,
            "output_precision": output_precision,
            "full_raw_matrix_shape": list(shape),
            "raw_smith_orders_all_fibers": histogram(measured),
            "weighted_newton_orders_per_fiber": histogram(predicted),
            "coefficient_minima_per_fiber": histogram(coefficient_weights),
            "attainable_cyclic_lengths_all_fibers": histogram(
                output_precision - max(0, order - loss) for order in measured
            ),
            "exact_width": len(measured),
            "coefficient_upper_bound": fibers * len(coefficient_weights),
        })
    return results


if __name__ == "__main__":
    cases = [
        (2, 3, 1, 0, 1),
        (2, 3, 1, 1, 1),
        (2, 4, 1, 1, 1),
        (2, 5, 1, 1, 1),
        (2, 3, 1, 1, 2),
        (2, 2, 2, 1, 1),
        (3, 2, 1, 1, 1),
    ]
    print(json.dumps(check(cases), indent=2))
