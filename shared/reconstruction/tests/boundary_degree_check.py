"""Independent primal and vanishing-polynomial tests of the paired boundary code.

The primal system starts with P(t)[u,v]=A_t[u,:]C[:,v] for each inaccessible
v. It eliminates the d unknown nonconstant coefficients for each (u,v)
separately by rational Vandermonde nullspace computations. The second system
uses divisibility on the complement of these slot sets and a coefficient
matrix for polynomials in ker C. Both see all 4**q physical coordinates.
"""
from functools import lru_cache
from itertools import product

from sympy import Matrix, zeros
from sympy.polys.matrices import DomainMatrix


def rank(a):
    return DomainMatrix.from_Matrix(a).rank()


def physical_matrix(q):
    letters = list(range(2**q))
    physical = list(product(letters, repeat=2))
    k = (q + 1) // 2
    c = zeros(q + k + 2, len(physical))
    for v, (a, b) in enumerate(physical):
        equal = [t for t in range(q) if (a >> t) % 2 == (b >> t) % 2]
        if not equal:
            c[q + k + a.bit_count() % 2, v] = 1
        if len(equal) == 1:
            t = equal[0]
            c[t, v] = 1
            c[q + t // 2, v] = (a >> t) % 2
    return c, physical


def primal_all(c, physical, q, labels, degree, desired_second):
    """Eliminate each entry's nonconstant polynomial coefficients from the primal."""
    variables = q * c.rows
    target = {i: j for j, i in enumerate(
        i for i, (_, b) in enumerate(physical) if b == desired_second)}
    coeff = []
    rhs = []

    @lru_cache(None)
    def moments(slot_set):
        f = Matrix(degree, len(slot_set), lambda i, j: labels[slot_set[j]] ** (i + 1))
        return f.nullspace()

    for v, (first, _) in enumerate(physical):
        slots = tuple(t for t in range(q)
                      if (first >> t) % 2 != (desired_second >> t) % 2)
        for weights in moments(slots):
            row = [0] * variables
            for t, w in zip(slots, weights):
                for i in range(c.rows):
                    row[t * c.rows + i] = w * c[i, v]
            vals = [0] * len(target)
            if v in target:
                vals[target[v]] = sum(weights)
            if any(row) or any(vals):
                coeff.append(row)
                rhs.append(vals)
    a = Matrix(len(coeff), variables, [z for row in coeff for z in row])
    b = Matrix(len(rhs), len(target), [z for row in rhs for z in row])
    return rank(a) == rank(a.row_join(b))


def dual_all(c, physical, q, labels, degree, desired_second):
    """Direct fixed-C criterion, formed from roots at every accessible group."""
    max_degree = q - degree - 1
    target = {i: j for j, i in enumerate(
        i for i, (_, b) in enumerate(physical) if b == desired_second)}
    columns = []
    test = []
    for v, (first, _) in enumerate(physical):
        roots = [labels[t] for t in range(q)
                 if (first >> t) % 2 == (desired_second >> t) % 2]
        if len(roots) > max_degree:
            continue
        polynomial = [1]
        for root in roots:
            result = [0] * (len(polynomial) + 1)
            for i, coefficient in enumerate(polynomial):
                result[i] -= root * coefficient
                result[i + 1] += coefficient
            polynomial = result
        for shift in range(max_degree - len(roots) + 1):
            values = ([0] * shift + polynomial + [0] * max_degree)[:max_degree + 1]
            col = [w * c[i, v] for w in values for i in range(c.rows)]
            tgt = [0] * len(target)
            if v in target and shift == 0:
                tgt[target[v]] = polynomial[0]
            if any(col) or any(tgt):
                columns.append(col)
                test.append(tgt)
    a = Matrix(len(columns), (max_degree + 1) * c.rows,
               [value for row in columns for value in row])
    rhs = Matrix(len(columns), len(target), [value for row in test for value in row])
    return rank(a) == rank(a.row_join(rhs))


def verify():
    for q in (2, 3, 4):
        c, physical = physical_matrix(q)
        assert rank(c) == q + (q + 1) // 2 + 2
        assert all(x in (-1, 0, 1) for x in c)
        labels = tuple(2 + 3 * t for t in range(q))
        degree = q - 2
        for tag, instance, cap in (
            ('construction', c, degree),
            ('delete one broadcast row', c[:-1, :], degree),
            *([('decrease degree', c, degree - 1)] if degree else []),
        ):
            passed = []
            for second in range(2**q):
                primal = primal_all(instance, physical, q, labels, cap, second)
                dual = dual_all(instance, physical, q, labels, cap, second)
                assert primal == dual, (q, tag, second, primal, dual)
                passed.append(primal)
            assert all(passed) == (tag == 'construction')
            print(f'q={q} d={cap} rank={rank(instance)} {tag}: '
                  f'{sum(passed)}/{len(passed)} second-word blocks feasible, '
                  'primal = dual', flush=True)


if __name__ == '__main__':
    verify()
