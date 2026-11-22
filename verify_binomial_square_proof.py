"""Exact polynomial certificates for the square-binomial q-log-convexity proof.

Run with Python 3. No external libraries are required. All coefficients are
rational numbers represented exactly. The checks cover unbounded real domains.
"""

from collections import defaultdict
from fractions import Fraction
from math import comb


class Polynomial:
    """A sparse polynomial in two variables with rational coefficients."""

    def __init__(self, terms):
        self.terms = {degree: Fraction(value) for degree, value in terms.items() if value}

    @staticmethod
    def coerce(value):
        if isinstance(value, Polynomial):
            return value
        return Polynomial({(0, 0): value})

    def __add__(self, value):
        terms = defaultdict(Fraction, self.terms)
        for degree, coefficient in self.coerce(value).terms.items():
            terms[degree] += coefficient
        return Polynomial(terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({degree: -value for degree, value in self.terms.items()})

    def __sub__(self, value):
        return self + (-self.coerce(value))

    def __rsub__(self, value):
        return self.coerce(value) + (-self)

    def __mul__(self, value):
        terms = defaultdict(Fraction)
        for (i, j), left in self.terms.items():
            for (k, m), right in self.coerce(value).terms.items():
                terms[i + k, j + m] += left * right
        return Polynomial(terms)

    __rmul__ = __mul__

    def __truediv__(self, constant):
        return self * (1 / Fraction(constant))

    def __pow__(self, exponent):
        result = self.coerce(1)
        for _ in range(exponent):
            result = result * self
        return result


def numerators(s, ell):
    """Return the three cleared numerators from the proof."""
    n = s + ell
    d = 2 * n - s
    e = d - 1
    z = d / 2
    a = n + z
    m = (2 * n + 1) * a + n
    v = 4 * (3 * a * z - 2 * n)

    u = d * (-4 * n * a + 2 * n**2 - 2 * n) + 4 * (n + 1) * n**2
    v0 = -(2 * n + 1) * d + m * (8 * n + 2)
    v4 = -(32 * n + 48) * a * z + 16 * n + 24 * n**2
    v6 = 32 * n + 24

    h0 = (d * (4 * n**2 * (2 * n + 1) * ell)**2
          - d * e**2 * (n * d * (d + 1))**2
          - 8 * n**2 * ell**2 * (s + 1) * m * e**2)
    h1 = -8 * n**2 * ell**2 * (s + 1) * s * (s + 2)

    m2 = s * (s + 1) * (s + 2) / 12
    m4 = m2 * (3 * s**2 + 6 * s - 4) / 20
    m6 = m2 * (3 * s**4 + 12 * s**3 - 24 * s + 16) / 112

    lower0 = h0 + e**2 * (a * u * m2 + v0 * m4)
    lower1 = d * v * h0 + d * e**2 * v * v0 * m4 - e**2 * u * (h1 + v4 * m4 + v6 * m6)
    quartic1 = d * v * v0 - u * v4
    return lower0, lower1, quartic1


def require_positive_coefficients(name, terms):
    if any(coefficient < 0 for coefficient in terms.values()):
        raise ArithmeticError(f"{name}: found a negative coefficient")
    if terms.get((0, 0), 0) <= 0:
        raise ArithmeticError(f"{name}: constant coefficient is not positive")
    print(f"{name}: verified {sum(bool(c) for c in terms.values())} nonzero coefficients")


def transform(polynomial, lower_interval):
    """Replace r by t/(16(1+t)) or by (1+t)/16, respectively."""
    # For the first interval clear (1+t)^m separately for each x-degree.
    degrees = defaultdict(int)
    for i, j in polynomial.terms:
        degrees[i] = max(degrees[i], j)

    terms = defaultdict(Fraction)
    for (i, j), coefficient in polynomial.terms.items():
        degree = degrees[i] - j if lower_interval else j
        offset = j if lower_interval else 0
        for k in range(degree + 1):
            terms[i, k + offset] += coefficient * Fraction(comb(degree, k), 16**j)
    return terms


def main():
    x = Polynomial({(1, 0): 1})
    y = Polynomial({(0, 1): 1})
    s = x + 2

    # For the quartic coefficient keep ell as an independent variable.
    _, _, quartic = numerators(s, y)
    require_positive_coefficients("quartic", quartic.terms)

    # For the lower bounds put ell = r*s^2. The two intervals cover r >= 0.
    lower0, lower1, _ = numerators(s, y * s**2)
    for name, lower in [("lower0", lower0), ("lower1", lower1)]:
        require_positive_coefficients(name + " on [0,1/16)", transform(lower, True))
        require_positive_coefficients(name + " on [1/16,infinity)", transform(lower, False))


if __name__ == "__main__":
    main()
