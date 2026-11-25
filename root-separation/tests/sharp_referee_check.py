"""Independent finite stress checks for the pinned-CNF root bound."""

from fractions import Fraction as F
from math import comb


def huber(x):
    if abs(x) <= 4:
        return x * x / 2
    return 4 * abs(x) - 8


def slope(x):
    return max(-4, min(4, x)) / F(4)


def biased_correlated_huber():
    # Two identical biased bits, and 298 independent fair bits.  Relative to
    # the product-uniform reference, the two admitted pairs have densities 3,1.
    k, n, h = 300, 298, 30
    eta = F(1, 4)
    targets = [F(0), F(0), F(0)]
    objectives = {pair_sign_sum: F(0) for pair_sign_sum in (-2, 0, 2)}
    clipped = F(0)
    through_boundary = F(0)
    population = 4 * (1 << n)
    centered_mean = F(0)
    second = F(0)
    assert h * h == 3 * k
    for ones in range(n + 1):
        sign_sum = 2 * ones - n
        for pair_bit, integer_weight in ((0, 1), (1, 3)):
            probability = F(integer_weight * comb(n, ones), population)
            pair_feature = pair_bit - F(3, 4)
            for pair_sign_sum in objectives:
                w = (F(sign_sum, 2) + pair_sign_sum * pair_feature) / h
                objectives[pair_sign_sum] += probability * huber(w)
            w = (F(sign_sum, 2) + 2 * pair_feature) / h
            b = slope(w)
            centered_mean += probability * w
            second += probability * w * w
            targets[0] += probability * b * pair_feature
            # Conditional on its sum, any one of the fair signs has this mean.
            targets[1] += probability * b * F(sign_sum, 2 * n)
            targets[2] += probability * (abs(w) <= 2)
            if abs(w) > 4:
                clipped += probability
            flip = w - 2 * pair_feature / h
            if min(abs(w), abs(flip)) < 4 < max(abs(w), abs(flip)):
                through_boundary += probability
            assert huber(flip) - huber(w) >= -4 * b * (w - flip) + (w - flip) ** 2 / 2 * (abs(w) <= 2)
    assert centered_mean == 0 and second <= 1 and targets[2] >= F(3, 4)
    assert objectives[-2] == objectives[2] > objectives[0]
    assert clipped > 0 and through_boundary > 0
    lower = 3 * eta * eta / (16 * h)
    assert min(targets[:2]) >= lower
    print('hubercase dimensions', k, 'domination', 3, 'H', h)
    print('E_mu (Y/H)^2', second, 'guaranteed minimum', lower)
    print('pair and independent-coordinate correlations', *(f'{float(q):.12g}' for q in targets[:2]))
    print('clipped and boundary-crossing masses', f'{float(clipped):.8g}', f'{float(through_boundary):.8g}')


def compensating_label_laws():
    for r, allowed in ((64, 32), (64, 7), (10, 1), (3, 1)):
        uniform = F(1, r)
        pins = [F(1, allowed) if g < allowed else F(0) for g in range(r)]
        other = [(10 * uniform - p) / 9 for p in pins]
        assert min(other) >= 0 and sum(other) == 1
        expected_pair_law = [(pins[g] + 9 * other[g]) * uniform / 10
                             for g in range(r) for _ in range(r)]
        assert all(weight == uniform * uniform for weight in expected_pair_law)
        print('uniform expected cells', r * r, 'symbols occupied by pins', allowed, 'of', r)


def contrast_constants():
    for r in range(2, 129):
        h, ell = r // 2, r - r // 2
        one_mass = F(h, r)
        two_mass = F(h * (h - 1), r * (r - 1))
        # Multiply each contrast value by sqrt(h*ell) before expanding.
        diag = (r * r * one_mass - 2 * r * h * one_mass + h * h) / (h * ell)
        off = (r * r * two_mass - 2 * r * h * one_mass + h * h) / (h * ell)
        assert diag == 1 and off == -F(1, r - 1)
    delta = 39 * (F(39, 41) - F(3, 10)) - 19
    assert delta > 0 and delta * delta > 38
    assert (F(63, 4) - 10) ** 2 > 20
    print('permutation second moments r=2..128 and endpoint defect bounds verified')


if __name__ == '__main__':
    biased_correlated_huber()
    compensating_label_laws()
    contrast_constants()
