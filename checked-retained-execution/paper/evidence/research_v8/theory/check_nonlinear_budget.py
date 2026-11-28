"""Compare nonlinear frontier capacities with raw polynomial evaluation matrices."""

import argparse
import json
from collections import Counter
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod
from pathlib import Path

import numpy as np


def valuation(n, prime, zero_value):
    if n == 0:
        return zero_value
    result = 0
    while n % prime == 0:
        n //= prime
        result += 1
    return result


def factorial_weight(n, q):
    total = 0
    while n:
        n //= q
        total += n
    return total


class ChainRing:
    """Small prime-power rings and the unramified dyadic quadratic extension."""

    def __init__(self, prime, precision, extension=1):
        assert extension == 1 or (prime, extension) == (2, 2)
        self.prime = prime
        self.precision = precision
        self.extension = extension
        self.q = prime**extension
        self.modulus = prime**precision
        self.size = self.modulus**extension
        m = self.modulus
        ids = np.arange(self.size)
        a, b = ids % m, ids // m
        ac = a[:, None] * a
        bd = b[:, None] * b
        # In the quadratic case theta^2 = -1-theta.
        self.plus = (a[:, None] + a) % m + m * ((b[:, None] + b) % m)
        self.minus = (a[:, None] - a) % m + m * ((b[:, None] - b) % m)
        self.times = (ac - bd) % m + m * (
            (a[:, None] * b + b[:, None] * a - bd) % m
        )
        self.values = np.array([
            min(valuation(x, prime, precision), valuation(y, prime, precision))
            for x, y in zip(a.tolist(), b.tolist())
        ])
        self.inverses = {
            index: int(np.flatnonzero(row == 1)[0])
            for index, row in enumerate(self.times)
            if self.values[index] == 0
        }
        self.quotients = [
            a // (prime**exponent) + m * (b // (prime**exponent))
            for exponent in range(precision)
        ]


def smith_profile(matrix, ring):
    """Smith valuations below the precision, starting from raw entries only."""
    a = matrix.copy()
    result = []
    for index in range(min(a.shape)):
        block = a[index:, index:]
        values = ring.values[block]
        pos = int(np.argmin(values))
        exponent = int(values.flat[pos])
        if exponent == ring.precision:
            break
        row, col = np.unravel_index(pos, block.shape)
        row, col = index + row, index + col
        a[[index, row], :] = a[[row, index], :]
        a[:, [index, col]] = a[:, [col, index]]
        unit = int(ring.quotients[exponent][a[index, index]])
        a[index, index:] = ring.times[ring.inverses[unit], a[index, index:]]
        assert a[index, index] == ring.prime**exponent
        multipliers = ring.quotients[exponent][a[index + 1 :, index]]
        removed = ring.times[multipliers[:, None], a[index, index + 1 :]]
        a[index + 1 :, index + 1 :] = ring.minus[a[index + 1 :, index + 1 :], removed]
        # The pivot column now vanishes below the pivot. Clearing its row
        # by column operations leaves the remaining block unchanged.
        a[index + 1 :, index] = 0
        result.append(exponent)
    return result


def scalar_matrix(points, ring):
    """Integral monomial basis modulo each coordinate's monic annihilator."""
    degrees = [len(set(axis)) for axis in zip(*points)]
    powers = list(product(*(range(n) for n in degrees)))
    return np.array([
        [
            prod(pow(x, d, ring.modulus) for x, d in zip(point, power)) % ring.modulus
            for power in powers
        ]
        for point in points
    ])


def scalar_checks():
    cases = [
        (2, 4, [8], [0]),
        (2, 5, [4, 5], [0, 0]),
        (2, 5, [5, 3], [1, 0]),
        (3, 3, [7], [0]),
        (5, 2, [6, 3], [0, 0]),
    ]
    results = []
    for prime, precision, sizes, shifts in cases:
        ring = ChainRing(prime, precision)
        indices = list(product(*(range(size) for size in sizes)))
        points = [
            tuple(3 + prime**shift * n for n, shift in zip(index, shifts))
            for index in indices
        ]
        measured = smith_profile(scalar_matrix(points, ring), ring)
        predicted = sorted(
            sum(n * shift + factorial_weight(n, prime) for n, shift in zip(index, shifts))
            for index in indices
        )
        assert measured == [v for v in predicted if v < precision]
        results.append({
            "q": prime, "precision": precision, "grid": sizes,
            "congruence_orders": shifts, "valuation_counts": dict(Counter(measured)),
        })
    ring = ChainRing(2, 4)
    duplicated = [(i, i) for i in range(7)]
    single = [(i,) for i in range(7)]
    assert smith_profile(scalar_matrix(duplicated, ring), ring) == smith_profile(
        scalar_matrix(single, ring), ring
    )
    # The four low-precision points lie in the same constant-residue fiber.
    # Exhaustively enumerate receiver polynomial columns, impose the indicated
    # exact divisibility, then compute the residue rank without Smith theory.
    points = [(0, 0), (2, 0), (0, 2), (2, 2)]
    brute = []
    for loss in (0, 1, 2):
        modulus = 2 ** (loss + 1)
        raw = scalar_matrix(points, ChainRing(2, loss + 1))
        seen = set()
        for coeff in product(range(modulus), repeat=4):
            value = raw @ np.array(coeff) % modulus
            if np.all(value % 2**loss == 0):
                seen.add(tuple((value // 2**loss).tolist()))
        assert len(seen) == 2 ** (1, 3, 4)[loss]
        brute.append({"loss": loss, "distinct_residue_columns": len(seen)})
    return {"grids": results, "correlated_registers_checked": True, "exhaustive": brute}


def jet_multiply(left, right, ring):
    """Batched product of ordinary coefficient arrays in A[z]/z^k."""
    nrows, k = left.shape
    result = np.zeros((nrows, k), dtype=int)
    for degree in range(k):
        value = np.zeros(nrows, dtype=int)
        for i in range(degree + 1):
            value = ring.plus[value, ring.times[left[:, i], right[:, degree - i]]]
        result[:, degree] = value
    return result


def raw_jet_matrix(ring, k, h, digit_rows=False):
    """All raw power columns, independent of the theorem's feature expansion."""
    if digit_rows:
        # Full choices for the constant coefficient, one residue digit for
        # every higher coefficient. The subset is labeled in the output.
        residue_reps = (
            list(range(ring.prime))
            if ring.extension == 1
            else [a + ring.modulus * b for a, b in product(range(2), repeat=2)]
        )
        jets = list(product(range(ring.size), *(residue_reps for _ in range(k - 1))))
    else:
        jets = list(product(range(ring.size), repeat=k))
    jets = np.array(jets, dtype=int)
    # The product of (T-a) over scalar residue lifts is in (pi,z) at
    # every jet. Its (P+k-1)-th power is a monic null polynomial.
    degree = ring.q * (ring.precision + k - 1)
    one = np.zeros_like(jets)
    one[:, 0] = 1
    powers = [one]
    for _ in range(1, degree):
        powers.append(jet_multiply(powers[-1], jets, ring))
    inputs = np.array(list(product(range(len(jets)), repeat=h)), dtype=int)
    cols = []
    for exponents in product(range(degree), repeat=h):
        value = powers[exponents[0]][inputs[:, 0]]
        for i in range(1, h):
            value = jet_multiply(value, powers[exponents[i]][inputs[:, i]], ring)
        # Arbitrary jet coefficients permit all coordinate projections.
        cols.append(value)
    return np.concatenate(cols, axis=1)


@lru_cache(maxsize=None)
def compositions(total, slots):
    if slots == 1:
        return [(total,)]
    return [
        (first,) + rest
        for first in range(total + 1)
        for rest in compositions(total - first, slots - 1)
    ]


def theoretical_jet_profile(ring, k, h):
    result = []
    degree = ring.precision + k - 2
    for total in range(degree + 1):
        for alpha in compositions(total, h):
            weights = [ring.precision] * k
            for rows in product(*(compositions(a, k) for a in alpha)):
                jet_degree = sum(sum(r * v for r, v in enumerate(row)) for row in rows)
                if jet_degree >= k:
                    continue
                weight = sum(row[0] for row in rows)
                for row in rows:
                    coefficient = factorial(sum(row)) // prod(factorial(b) for b in row)
                    weight += valuation(coefficient, ring.prime, ring.precision)
                weights[jet_degree] = min(weights[jet_degree], weight)
            result.extend(w for w in weights if w < ring.precision)
    return sorted(result * ring.q**h)


def jet_checks():
    # q, precision, length, distinct messages, residue-digit rows only.
    cases = [
        (2, 1, 2, 2, False),
        (3, 1, 3, 2, False),
        (4, 1, 4, 1, False),
        (3, 2, 2, 2, False),
        (4, 2, 3, 1, False),
        (4, 3, 2, 1, False),
        (5, 2, 3, 1, True),
        # q < k gives a strict failure of unqualified equality.
        (2, 1, 3, 1, False),
    ]
    results = []
    for q, precision, k, h, digit_rows in cases:
        prime, ext = (2, 2) if q == 4 else (q, 1)
        ring = ChainRing(prime, precision, ext)
        raw = raw_jet_matrix(ring, k, h, digit_rows)
        actual = smith_profile(raw, ring)
        predicted = theoretical_jet_profile(ring, k, h)
        if q > precision + k - 2:
            assert actual == predicted, (q, precision, k, h, actual, predicted)
        else:
            assert len(actual) == 6 and len(predicted) == 8
        results.append({
            "q": q, "precision": precision, "k": k, "messages": h,
            "row_domain": "single higher-coefficient digit" if digit_rows else "full",
            "raw_matrix_shape": list(raw.shape),
            "measured_valuation_counts": dict(Counter(actual)),
            "predicted_bound_by_valuation": dict(Counter(predicted)),
        })
    return results


def packed_equality():
    results = []
    ring = ChainRing(2, 1)
    for bits in range(1, 7):
        n = 2**bits
        normalized = np.array([
            [comb(x, j) % 2 if j <= x else 0 for j in range(n)] for x in range(n)
        ])
        assert smith_profile(normalized, ring) == [0] * n
        loss = factorial_weight(n - 1, 2)
        assert loss == n - 1 - bits
        results.append({"sender_bits": bits, "full_residue_rank": n, "least_loss": loss})
    return results


def digit_and_trace_checks():
    digits = []
    for bit in range(7):
        index = 2**bit
        loss = factorial_weight(index, 2)
        assert loss == index - 1
        for x in range(4 * index + 3):
            value = comb(x, index) % 2 if x >= index else 0
            assert value == ((x >> bit) & 1)
        digits.append({"bit_index": bit, "least_loss": loss})

    trace_cases = []
    for precision in range(1, 5):
        ring = ChainRing(2, precision, extension=2)
        modulus = ring.modulus
        # In F_4 with theta^2+theta+1=0 the trace dual to (1,theta)
        # is (1+theta,1). The same coefficients can be lifted at any precision.
        exponent = precision * (ring.q - 1) * ring.q ** (precision - 1)
        for u in range(ring.size):
            for expected, beta in zip(
                (u % modulus % 2, u // modulus % 2), (1 + modulus, 1)
            ):
                t = int(ring.times[beta, u])
                t = int(ring.plus[t, ring.times[t, t]])
                value, factor, n = 1, t, exponent
                while n:
                    if n & 1:
                        value = int(ring.times[value, factor])
                    factor = int(ring.times[factor, factor])
                    n //= 2
                assert value == expected
        trace_cases.append({
            "precision": precision, "all_input_scalars": ring.size,
            "scalar_outputs_exactly_zero_or_one": 2 * ring.size,
        })
    return {"high_binary_digits": digits, "quadratic_unramified_trace": trace_cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "scalar": scalar_checks(),
        "jets": jet_checks(),
        "packed_integer_equality": packed_equality(),
        "coordinate_extractors": digit_and_trace_checks(),
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
