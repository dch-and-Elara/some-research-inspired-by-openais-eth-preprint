"""Compute the exact worst-input prefix on one specified rational arithmetic progression."""
from argparse import ArgumentParser
from fractions import Fraction


def minimum_prefix(start, step, terms):
    if terms < 1 or not step:
        raise ValueError("Positive sparsity and nonzero step are required")
    z = Fraction(start)/Fraction(step)
    k = 2*terms
    if (2*z).denominator != 1 or z + k-1 < 0:
        return k
    positive_start = max(0, (-z).__floor__()+1)
    return positive_start + k


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("start",type=Fraction)
    parser.add_argument("step",type=Fraction)
    parser.add_argument("terms",type=int)
    args = parser.parse_args()
    print(minimum_prefix(args.start,args.step,args.terms))
