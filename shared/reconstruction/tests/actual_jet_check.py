"""Check the signed unit-clause jet span and separated diagonal target exactly.

Run with Python 3 from any directory. The sibling actual_layout_check module
supplies integer Gaussian elimination with gcd reduction. No external packages
are needed.
"""

from math import comb

from actual_layout_check import rank


def multiply_to_order(left, right, order):
    """Product in Z[z] modulo z**(order+1)."""
    return [
        sum(left[j] * right[degree-j] for j in range(degree + 1))
        for degree in range(order + 1)
    ]


def second_occurrence_coefficient(positive_literals, y, variables, order):
    """Return s**n times the order-s coefficient for the n second clauses."""
    polynomial = [1] + [0] * order
    for i in range(variables):
        positive = bool(positive_literals & (1 << i))
        y_i = int(bool(y & (1 << i)))
        # b(z)=sum_{j=1}^s (-z)^j/s. A positive unit clause is b(z)*y_i,
        # and a negative one is 1-b(z)*y_i. Scale each by s.
        factor = [0 if positive else order]
        literal_sign = 1 if positive else -1
        factor.extend(literal_sign * y_i * (-1)**j
                      for j in range(1, order + 1))
        polynomial = multiply_to_order(polynomial, factor, order)
    return polynomial[order]


def first_occurrence_indicator(positive_literals, assignment, variables):
    for i in range(variables):
        selected = bool(positive_literals & (1 << i))
        assigned = bool(assignment & (1 << i))
        if selected != assigned:
            return 0
    return 1


def check_parameters(variables, order):
    cube = range(2**variables)
    expected = sum(comb(variables, h) for h in range(1, order + 1))

    # Exhaust the second-literal signs and Boolean probes. Distinct first signs
    # specify disjoint rows x, a fact checked directly in the next loop.
    second_rows = [
        [second_occurrence_coefficient(signs, y, variables, order) for y in cube]
        for signs in cube
    ]
    second_rank = rank(second_rows)
    assert second_rank == expected

    actual_rows = []
    for first_signs in cube:
        indicators = [first_occurrence_indicator(first_signs, x, variables)
                      for x in cube]
        assert sum(indicators) == 1 and indicators[first_signs] == 1
        for second_row in second_rows:
            # Columns (x,y) are the physical assignment and Boolean probe.
            actual_rows.append([indicator * value for indicator in indicators
                                for value in second_row])
    formula_count = len(actual_rows)
    actual_rank = rank(actual_rows)
    assert formula_count == 4**variables
    assert actual_rank == 2**variables * expected

    # Evaluate the diagonal on the signed-family span tests
    # 1_{x=c} b(z)^h Y_S. Check the scalar coefficient independently first.
    scaled_b = [0] + [(-1)**j for j in range(1, order + 1)]
    power = [1] + [0] * order
    weight = {}
    for h in range(1, order + 1):
        power = multiply_to_order(power, scaled_b, order)
        assert power[order] == (-1)**order * comb(order - 1, h - 1)
        weight[h] = order**(variables-h) * power[order]

    supports = [mask for mask in cube if 1 <= mask.bit_count() <= order]
    diagonal_rows = [
        [weight[mask.bit_count()] if mask & c == mask else 0 for mask in supports]
        for c in cube
    ]
    diagonal_rank = rank(diagonal_rows)
    assert diagonal_rank == expected
    return formula_count, second_rank, actual_rank, diagonal_rank


def main():
    pairs = 0
    input_count = 0
    print("n s signed_formulas second_sign_rank actual_array_rank diagonal_rank B_s-1")
    for variables in range(1, 5):
        for order in range(1, variables + 1):
            count, second_rank, actual_rank, diagonal_rank = check_parameters(
                variables, order
            )
            expected = sum(comb(variables, h) for h in range(1, order + 1))
            print(variables, order, count, second_rank, actual_rank,
                  diagonal_rank, expected)
            pairs += 1
            input_count += count
    print(f"PASS: {pairs} parameter pairs; {input_count} parameter-tagged "
          "signed formulas. All ranks and coefficient checks are exact.")


if __name__ == "__main__":
    main()
