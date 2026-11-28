"""Exact finite checks for the native-register note, using only Python's standard library."""
from fractions import Fraction
from itertools import product
import json
import math
from random import Random


def linear_product(factors):
    coeffs = [Fraction(1)]
    for a, b in factors:
        expanded = [Fraction(0)] * (len(coeffs) + 1)
        for j, c in enumerate(coeffs):
            expanded[j] += c * a
            expanded[j + 1] += c * b
        coeffs = expanded
    return coeffs


def val2(n):
    assert n
    n = abs(n)
    return (n & -n).bit_length() - 1


def check_kernel():
    count, coefficients = 0, 0
    for a in range(1, 4):
        L, alpha = 2**a, 2**(a + 1)
        S = tuple(range(-L, L))
        d0 = math.prod(-d for d in S if d)
        for t in S:
            if t == 0 or abs(t) == L:
                continue
            ct = Fraction(math.prod(t - d for d in S if d != t), d0)
            for q in range(1 - L, L):
                direct = [c / d0 for c in linear_product((t - d, alpha) for d in S if d != q)]
                factors = [(1, Fraction(alpha, t - d)) for d in S if d not in {t, q}]
                if q != t:
                    factors += [(0, Fraction(alpha, t - q))]
                normalized = [ct * c for c in linear_product(factors)]
                assert direct == normalized
                assert direct[0] == (ct if q == t else 0)
                for j, v in enumerate(direct):
                    if v:
                        assert val2(v.numerator) - val2(v.denominator) >= j
                count += 1
                coefficients += len(direct)
    return {"kernels": count, "coefficients": coefficients}


OLD = (
    ("p0", (0,)), ("p1", (2,)), ("or", (4, 6)),
    ("imp", (8, 10)), ("imp", (12, 14)),
    ("eq", (1, 5, 16)), ("eq", (9, 15, 17)),
    ("eq", (3, 7, 18)), ("eq", (11, 13, 19)),
)
NEW = tuple(("eq", (2 * k, 2 * k + 1)) for k in range(10))


def extension(name, args, signs):
    if name.startswith("p"):
        x = args[0]
        return x if signs[int(name[1:])] else 1 - x
    if name == "or":
        x, y = args
        return x + y - x * y
    if name == "imp":
        x, y = args
        return 1 - x + x * y
    return math.prod(args) + math.prod(1 - x for x in args)


def packet_matching(packets, t):
    mapping = {}
    for packet in packets:
        for x, row in enumerate(packet):
            y = x + t
            if row is not None and 0 <= y < len(packet) and packet[y] is not None:
                mapping[row] = packet[y]
    return mapping


def sample_value(packets, signs, old_rows):
    matched = packet_matching(packets, -1)
    rows, cols = (OLD, NEW) if old_rows else (NEW, OLD)
    choices = []
    for name, ports in cols:
        choices.append([tuple(zip(ports, word)) for word in product(range(2), repeat=len(ports))
                        if extension(name, word, signs)])
    total = 0
    for column in product(*choices):
        bits = dict(p for chunk in column for p in chunk)
        weight = 1
        for name, ports in rows:
            args = [-bits[matched[x]] if x in matched else 0 for x in ports]
            weight *= extension(name, args, signs)
            if not weight:
                break
        total += weight
    return total


MASK = (1 << (1 << 10)) - 1
FREE = [sum(1 << j for j in range(1 << 10) if (j >> k) & 1) for k in range(10)]


def old_rows_parity(packets):
    matched = packet_matching(packets, -1)
    y = [FREE[matched[x] // 2] if x in matched else 0 for x in range(20)]
    keep = MASK
    for name, ports in OLD[2:]:
        x = [y[p] for p in ports]
        if name == "or":
            keep &= x[0] | x[1]
        elif name == "imp":
            keep &= (MASK ^ x[0]) | x[1]
        else:
            keep &= MASK ^ ((x[0] ^ x[1]) | (x[0] ^ x[2]))
    return [((keep & (y[0] if a else MASK ^ y[0]) &
              (y[2] if b else MASK ^ y[2])).bit_count() & 1)
            for a, b in product(range(2), repeat=2)]


def random_packets(rng, padded):
    slots = list(range(20)) + [None] * (4 if padded else 0)
    rng.shuffle(slots)
    return [slots[i:i+4] for i in range(0, len(slots), 4)]


def check_support():
    rng = Random(451)
    words = list(product(range(2), repeat=2))
    outcomes = set()
    for k in range(16):
        packets = random_packets(rng, k % 2)
        matched = packet_matching(packets, -1)
        for old_rows in (True, False):
            vals = [sample_value(packets, w, old_rows) for w in words]
            actual = [x != 0 for x in vals]
            if old_rows:
                assert [v % 2 for v in vals] == old_rows_parity(packets)
                expected = [any(x in matched for x in (4, 6))
                            and all(not w[j] or 2 * j in matched for j in (0, 1))
                            for w in words]
            else:
                expected = [True] * 4
            assert actual == expected
            outcomes.add(tuple(actual))
    witness = None
    for k in range(20000):
        packets = random_packets(rng, k % 2 == 1)
        if old_rows_parity(packets) == [0, 1, 1, 1]:
            vals = [sample_value(packets, w, True) for w in words]
            assert [v % 2 for v in vals] == [0, 1, 1, 1]
            witness = {"trial": k + 1, "packets": packets,
                       "integer_values_order_00_01_10_11": vals}
            break
    return {"layouts_both_orientations": 16, "sign_evaluations": 128,
            "different_integer_supports": len(outcomes), "parity_OR_witness": witness}


if __name__ == "__main__":
    result = {"cauchy": check_kernel(), "unit_shift": check_support()}
    print(json.dumps(result, indent=2))
