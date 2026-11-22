"""Verify the rising-binomial cubic proof using Python 3 and exact rationals."""

from collections import defaultdict
from fractions import Fraction
from math import factorial


class Polynomial:
    """A sparse polynomial in x, y, and t over the rational numbers."""

    def __init__(self, terms):
        self.terms = {index: Fraction(value) for index, value in terms.items() if value}

    @staticmethod
    def coerce(value):
        if isinstance(value, Polynomial):
            return value
        return Polynomial({(0, 0, 0): value})

    def __add__(self, other):
        terms = defaultdict(Fraction, self.terms)
        for index, coefficient in self.coerce(other).terms.items():
            terms[index] += coefficient
        return Polynomial(terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({index: -value for index, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        terms = defaultdict(Fraction)
        for (i, j, k), a in self.terms.items():
            for (r, s, v), b in self.coerce(other).terms.items():
                terms[i + r, j + s, k + v] += a * b
        return Polynomial(terms)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = self.coerce(1)
        for _ in range(exponent):
            result = result * self
        return result

    def coefficient(self, degree):
        return Polynomial({(i, j, 0): c for (i, j, k), c in self.terms.items() if k == degree})


x = Polynomial({(1, 0, 0): 1})
y = Polynomial({(0, 1, 0): 1})
t = Polynomial({(0, 0, 1): 1})


def require(condition, label):
    if not condition:
        raise ArithmeticError(label)


def positive_coefficients(polynomial, count, label):
    require(len(polynomial.terms) == count, label + ": term count")
    require(all(c > 0 for c in polynomial.terms.values()), label + ": coefficient sign")
    require(polynomial.terms.get((0, 0, 0), 0) > 0, label + ": constant term")
    print(f"{label}: {count} positive coefficients")


def rising_row(variable, degree):
    row = [Polynomial.coerce(1)]
    product = Polynomial.coerce(1)
    for k in range(1, degree + 1):
        product *= variable + k - 1
        row.append((product * Fraction(1, factorial(k))) ** 3)
    return row


def verify_initial_coefficients():
    u = x + 1
    formulas = [
        6 * u,
        Fraction(3, 4) * u * (u + 1) * (u**2 + 9 * u + 6),
        Fraction(1, 6) * u * (u + 1)**3 * (2 * u**3 - u**2 + 20 * u + 24),
    ]
    for d, formula in enumerate(formulas, 1):
        prev, curr, nxt = [rising_row(u + j, d) for j in (-1, 0, 1)]
        delta = sum(prev[i] * nxt[d - i] - curr[i] * curr[d - i] for i in range(d + 1))
        require(not (delta - formula).terms, f"degree {d}: closed form")
    print("Degrees 1-3: exact identities")


def elimination(n, z):
    a = n + z
    b = a * z
    positive = (a + t) * (a + 1 + t)
    negative = (a - t) * (a + 1 - t)
    A = Fraction(1, 2) * n**3 * (positive**3 + negative**3) - (n + 1)**3 * (a * a - t * t)**3

    U = (b - t * t - n * t)**3
    V = (b - t * t + n * t)**3
    f, g = 2 * t + 1, 2 * t - 1
    D = U * f - V * g
    E = U * (f**3 - f) - V * (g**3 - g)

    H = 2 * z * z
    u = (n + 1) * a
    C = 3 * u * u - 3 * u * z + z * z
    J = H * A + C * D
    F = E.coefficient(2)
    J2 = J.coefficient(2)
    require(not J.coefficient(0).terms and not E.coefficient(0).terms, "constant terms")
    require(not (F - 24 * b * b * (b - n)).terms, "quadratic term of E")

    S = F * J - J2 * E
    require(all(k in (4, 6, 8) for i, j, k in S.terms), "residual degrees")
    return H, C, F, J2, tuple(S.coefficient(i) for i in (4, 6, 8))


def verify_bernstein(label, residual, bound, count):
    r4, r6, r8 = residual
    controls = (r4, r4 + r6 * bound * Fraction(1, 2), r4 + r6 * bound + r8 * bound**2)
    for i, polynomial in enumerate(controls):
        positive_coefficients(polynomial, count, f"{label}, control {i}")


def moments(s):
    m2 = Fraction(1, 12) * s * (s + 1) * (s + 2)
    m4 = Fraction(1, 20) * m2 * (3 * s**2 + 6 * s - 4)
    m6 = Fraction(1, 112) * m2 * (3 * s**4 + 12 * s**3 - 24 * s + 16)
    m8 = Fraction(1, 960) * m2 * (
        5 * s**6 + 30 * s**5 + 20 * s**4 - 120 * s**3 - 16 * s**2 + 288 * s - 192
    )
    return m4, m6, m8


def verify_moments():
    for degree, prev, nxt, even_base, odd_base in zip(
        (4, 6, 8), moments(x), moments(x + 2), moments(0), moments(1)
    ):
        change = 2 * ((x + 2) * Fraction(1, 2)) ** degree
        require(not (nxt - prev - change).terms, f"moment {degree}: recurrence")
        require(even_base == 0 and odd_base == Fraction(2, 2**degree), f"moment {degree}: base cases")
    print("Moments 4, 6 and 8: recurrence and base cases")


def verify_boundary(H, C, F, J2, residual, s, l, n, d):
    boundary = (2 * n * l)**3 * 2 * (s + 1)
    r4, r6, r8 = residual
    m4, m6, m8 = moments(s)
    bound = (
        H * F * ((4 * n**2 * (2 * n + 1) * l)**3 - (n * d * (d + 1))**3 * (d - 1)**3)
        + (-F * C * boundary + J2 * boundary * s * (s + 2)
           + r4 * m4 + r6 * m6 + r8 * m8) * (d - 1)**3
    )

    terms = dict(bound.terms)
    triples = [
        ((3, 17, 0), (1, 18, 0), (5, 16, 0)),
        ((4, 16, 0), (2, 17, 0), (6, 15, 0)),
        ((5, 15, 0), (3, 16, 0), (7, 14, 0)),
    ]
    for middle, left, right in triples:
        target, a, b = terms.pop(middle), terms.pop(left), terms.pop(right)
        require(tuple(u + v for u, v in zip(left, right)) == tuple(2 * u for u in middle),
                "AM-GM midpoint")
        require(target < 0 and a > 0 and b > 0 and 4 * a * b >= target**2, "AM-GM coefficients")
    positive_coefficients(Polynomial(terms), 235, "Boundary remainder")


def verify_cubic():
    verify_initial_coefficients()
    verify_moments()
    z = 2 + x
    n = 2 * z + 1 + y
    *_, residual = elimination(n, z)
    verify_bernstein("Low degree", residual, z * z, 99)

    s, l = 2 + x, y
    n, z = s + l, s * Fraction(1, 2) + l
    H, C, F, J2, residual = elimination(n, z)
    verify_bernstein("High degree", residual, s * s * Fraction(1, 4), 105)
    verify_boundary(H, C, F, J2, residual, s, l, n, 2 * z)


def verify_fourth_power():
    a, b, c = x*x - x, x*x + x, x*x + 3*x + 2
    scaled = a**4 + c**4 - 2 * b**4 + 16 * ((x*x - 1)**4 - x**8)
    expected = -8*x**6 + 168*x**5 + 416*x**4 + 360*x**3 + 184*x**2 + 96*x + 32
    require(not (scaled - expected).terms, "fourth-power polynomial")
    require(sum(value * 24**i for (i, _, _), value in scaled.terms.items()) == -47_999_200,
            "fourth-power counterexample")
    print("Fourth power: exact polynomial and counterexample")


if __name__ == "__main__":
    verify_cubic()
    verify_fourth_power()
