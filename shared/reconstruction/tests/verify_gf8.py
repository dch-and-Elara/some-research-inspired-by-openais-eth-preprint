"""Test the proposed q-2 encoder against the original row recovery problem over GF(8)."""
from itertools import product


def multiply(x, y):
    z = 0
    while y:
        if y & 1:
            z ^= x
        x <<= 1
        if x & 8:
            x ^= 0b1011
        y >>= 1
    return z


MUL = [[multiply(x, y) for y in range(8)] for x in range(8)]
INV = [0] + [MUL[x].index(1) for x in range(1, 8)]


def rank(rows):
    pivots = {}
    for row in rows:
        row = list(row)
        for c in range(len(row)):
            x = row[c]
            if not x:
                continue
            if c not in pivots:
                pivots[c] = [MUL[INV[x]][y] for y in row]
                break
            row = [y ^ MUL[x][z] for y, z in zip(row, pivots[c])]
    return len(pivots)


def annihilator(sites, labels, d):
    # All constraints left on the caller's measurements after eliminating
    # the coefficients of X through X^d of one polynomial entry.
    for last in sites[d:]:
        coeff = {last: 1}
        for i in sites[:d]:
            weight = MUL[labels[last]][INV[labels[i]]]
            for j in sites[:d]:
                if i != j:
                    weight = MUL[weight][MUL[labels[last] ^ labels[j]][INV[labels[i] ^ labels[j]]]]
            coeff[i] = weight
        yield coeff


def feasible_centers(q, labels, omit):
    words = list(range(1 << q))
    mask = (1 << q) - 1
    k = (q + 1) // 2
    m = q + k + 2
    good = 0
    for b in words:
        # Solve for every output with this second word. Kernels and arbitrary
        # side-information rows are eliminated by restricting to unread inputs.
        equations = []
        for a, second in product(words, repeat=2):
            sites = [i for i in range(q) if (a ^ b) >> i & 1]
            if len(sites) <= q - 2:
                continue
            match = mask ^ a ^ second
            col = []
            if not match:
                col = [q + k + a.bit_count() % 2]
            elif match.bit_count() == 1:
                t = match.bit_length() - 1
                col = [t] + ([q + t // 2] if a >> t & 1 else [])
            for weights in annihilator(sites, labels, q - 2):
                row = [0] * (q * m + len(words))
                for t, x in weights.items():
                    for j in col:
                        if j != omit:
                            row[t*m + j] ^= x
                    if second == b:
                        row[q*m + a] ^= x
                equations.append(row)
        good += rank(row[:q*m] for row in equations) == rank(equations)
    return good


if __name__ == "__main__":
    for q in range(2, 6):
        for labels in (tuple(range(1, q+1)), (7, 3, 6, 2, 5)[:q]):
            full = feasible_centers(q, labels, None)
            drop = feasible_centers(q, labels, q + (q+1)//2 + 1)
            print(f"q={q}, labels={labels}, feasible blocks {full}/{2**q}, drop parity row {drop}/{2**q}")
            assert full == 2**q and drop == 2**(q-1)
