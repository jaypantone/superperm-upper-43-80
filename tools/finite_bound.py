#!/usr/bin/env python3
"""Evaluate the finite upper bound C(m, a) of Challenge.lean with exact
rational arithmetic, minimized over a.  This is arithmetic, not a proof.

    python3 tools/finite_bound.py 11 12 13 14 15
"""
import argparse
from fractions import Fraction
from math import factorial


def f3(k):
    return factorial(k) + factorial(k - 1) + factorial(k - 2)


def cost(m, a):
    """C(m, a) for m >= 9 and 2 <= a <= m; the word has m + 2 symbols."""
    h = m - 1
    connectors = Fraction(17, 240) * factorial(h) / h
    return (f3(m + 2) + Fraction(43, 80) * factorial(h) + (a - 2) * connectors
            + (m - a) * min(connectors, Fraction(factorial(m + 1), factorial(a + 1))))


def best(k):
    """The smallest bound at k >= 11 symbols, with its minimizing a."""
    m = k - 2
    a = min(range(2, m + 1), key=lambda a: cost(m, a))
    value = cost(m, a)
    return a, value.numerator // value.denominator


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("sizes", type=int, nargs="*", default=[11, 12, 13, 14, 15])
    args = parser.parse_args()
    for k in args.sizes:
        if k < 11:
            parser.error("the finite theorem applies for at least 11 symbols")
        a, bound = best(k)
        print(f"K={k}  a={a}  bound={bound:,}")


if __name__ == "__main__":
    main()
