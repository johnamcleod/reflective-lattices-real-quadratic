"""Exact arithmetic in K = Q, Q(sqrt2), Q(sqrt5) and their rings of integers O.

Representation
--------------
O has Z-basis (1, w) with w^2 = c0 + c1*w:
    Z        : D = 1   (w unused, b = 0 always)
    Z[sqrt2] : D = 2,  w = sqrt2, w^2 = 2          (c0, c1) = (2, 0), disc 8
    Z[phi]   : D = 5,  w = phi,   w^2 = 1 + phi    (c0, c1) = (1, 1), disc 5
An element of K is (a + b*w)/n with integers a, b, n, n > 0, gcd(a, b, n) = 1.
It lies in O iff n == 1 (because (1, w) is an integral basis).

Embeddings: id sends w to (c1 + sqrt(disc))/2 > 0, sigma to (c1 - sqrt(disc))/2.
All signs are decided exactly from 2(a + b*w) = (2a + b*c1) +- b*sqrt(disc).
"""
from __future__ import annotations

from math import gcd as igcd, isqrt
from typing import Dict, Iterable, List, Tuple


def _sign_xy(x: int, y: int, disc: int) -> int:
    """Exact sign of x + y*sqrt(disc) (disc > 0 not a square, or y == 0)."""
    if y == 0:
        return (x > 0) - (x < 0)
    if x >= 0 and y > 0:
        return 1
    if x <= 0 and y < 0:
        return -1
    # opposite signs (x != 0): compare x^2 with disc*y^2
    d = x * x - disc * y * y
    if d == 0:
        return 0  # impossible for non-square disc, kept for completeness
    return (1 if x > 0 else -1) if d > 0 else (1 if y > 0 else -1)


class Ring:
    """One of Z, Z[sqrt2], Z[phi]."""

    _DATA = {1: (0, 0, 1, "Z"), 2: (2, 0, 8, "Z[sqrt2]"), 5: (1, 1, 5, "Z[phi]")}

    def __init__(self, D: int):
        if D not in self._DATA:
            raise ValueError("D must be 1, 2 or 5")
        self.D = D
        self.c0, self.c1, self.disc, self.name = self._DATA[D]
        self.zero = El(self, 0, 0, 1)
        self.one = El(self, 1, 0, 1)
        self.w = El(self, 0, 1, 1) if D != 1 else None
        # fundamental unit (norm -1 for D = 2, 5); for Z there is none beyond -1
        self.eps = {1: self.one, 2: El(self, 1, 1, 1), 5: El(self, 0, 1, 1)}[D]
        self.eta = self.eps * self.eps  # generator of the totally positive units

    # construction ---------------------------------------------------------
    def __call__(self, a=0, b=0, n=1) -> "El":
        """a + b*w (over n). Accepts ints or Fractions for a, b."""
        from fractions import Fraction
        if isinstance(a, Fraction) or isinstance(b, Fraction):
            a, b = Fraction(a), Fraction(b)
            den = a.denominator * b.denominator // igcd(a.denominator, b.denominator)
            return El(self, int(a * den), int(b * den), den * n)
        return El(self, a, b, n)

    def __repr__(self):
        return f"Ring({self.name})"

    def __eq__(self, other):
        return isinstance(other, Ring) and other.D == self.D

    def __hash__(self):
        return hash(self.D)

    def __reduce__(self):
        return (get_ring, (self.D,))


_RINGS: Dict[int, Ring] = {}


def get_ring(D: int) -> Ring:
    if D not in _RINGS:
        _RINGS[D] = Ring(D)
    return _RINGS[D]




class El:
    """Element (a + b*w)/n of K."""

    __slots__ = ("R", "a", "b", "n")

    def __init__(self, R: Ring, a: int, b: int = 0, n: int = 1):
        if R.D == 1:
            b = 0
        if n < 0:
            a, b, n = -a, -b, -n
        if n == 0:
            raise ZeroDivisionError
        if n != 1:
            g = igcd(igcd(a, b), n)
            if g > 1:
                a, b, n = a // g, b // g, n // g
        self.R, self.a, self.b, self.n = R, a, b, n

    # arithmetic ------------------------------------------------------------
    def _c(self, o) -> "El":
        if isinstance(o, El):
            return o
        if isinstance(o, int):
            return El(self.R, o, 0, 1)
        from fractions import Fraction
        if isinstance(o, Fraction):
            return El(self.R, o.numerator, 0, o.denominator)
        raise TypeError(type(o))

    def __add__(s, o):
        o = s._c(o)
        if s.n == o.n:
            return El(s.R, s.a + o.a, s.b + o.b, s.n)
        return El(s.R, s.a * o.n + o.a * s.n, s.b * o.n + o.b * s.n, s.n * o.n)

    __radd__ = __add__

    def __neg__(s):
        return El(s.R, -s.a, -s.b, s.n)

    def __sub__(s, o):
        return s + (-s._c(o))

    def __rsub__(s, o):
        return s._c(o) - s

    def __mul__(s, o):
        o = s._c(o)
        R = s.R
        bd = s.b * o.b
        return El(R, s.a * o.a + R.c0 * bd, s.a * o.b + s.b * o.a + R.c1 * bd, s.n * o.n)

    __rmul__ = __mul__

    def conj(s) -> "El":
        if s.R.D == 1:
            return s
        return El(s.R, s.a + s.R.c1 * s.b, -s.b, s.n)

    def norm_num(s) -> int:
        """Numerator of the norm: N(a + b w) (without the n^2)."""
        R = s.R
        if R.D == 1:
            return s.a          # the norm of K = Q over Q is the identity
        return s.a * s.a + R.c1 * s.a * s.b - R.c0 * s.b * s.b

    def norm(s):
        from fractions import Fraction
        return Fraction(s.norm_num(), s.n if s.R.D == 1 else s.n * s.n)

    def trace(s):
        from fractions import Fraction
        return Fraction(2 * s.a + s.R.c1 * s.b, s.n)

    def inv(s) -> "El":
        if s.R.D == 1:
            if s.a == 0:
                raise ZeroDivisionError
            return El(s.R, s.n, 0, s.a)
        N = s.norm_num()
        if N == 0:
            raise ZeroDivisionError
        c = s.conj()
        # 1/((a+bw)/n) = n * conj(a+bw) / N
        return El(s.R, c.a * s.n, c.b * s.n, N)

    def __truediv__(s, o):
        return s * s._c(o).inv()

    def __rtruediv__(s, o):
        return s._c(o) * s.inv()

    def __pow__(s, k: int):
        r = s.R.one
        b = s if k >= 0 else s.inv()
        for _ in range(abs(k)):
            r = r * b
        return r

    # predicates -------------------------------------------------------------
    def __eq__(s, o):
        if not isinstance(o, El):
            try:
                o = s._c(o)
            except TypeError:
                return NotImplemented
        return s.a == o.a and s.b == o.b and s.n == o.n

    def __hash__(s):
        return hash((s.a, s.b, s.n))

    def is_zero(s) -> bool:
        return s.a == 0 and s.b == 0

    def is_integral(s) -> bool:
        return s.n == 1

    def is_unit(s) -> bool:
        return s.n == 1 and not s.is_zero() and abs(s.norm_num()) == 1

    def sign(s) -> int:
        """Sign at id (exact)."""
        R = s.R
        if R.D == 1:
            return (s.a > 0) - (s.a < 0)
        return _sign_xy(2 * s.a + R.c1 * s.b, s.b, R.disc)

    def ssign(s) -> int:
        """Sign at sigma (exact)."""
        R = s.R
        if R.D == 1:
            return s.sign()
        return _sign_xy(2 * s.a + R.c1 * s.b, -s.b, R.disc)

    def tpos(s) -> bool:
        return s.sign() > 0 and (s.R.D == 1 or s.ssign() > 0)

    # conversions ------------------------------------------------------------
    def __float__(s):
        R = s.R
        if R.D == 1:
            return s.a / s.n
        return (s.a + s.b * (R.c1 + R.disc ** 0.5) / 2) / s.n

    def sfloat(s):
        return float(s.conj())

    def coords(self) -> Tuple[int, int, int]:
        return (self.a, self.b, self.n)

    def to_json(self):
        return [self.a, self.b] if self.n == 1 else [self.a, self.b, self.n]

    def __repr__(s):
        R = s.R
        w = {1: "", 2: "√2", 5: "φ"}[R.D]
        if s.b == 0:
            core = f"{s.a}"
        elif s.a == 0:
            core = f"{s.b}{w}"
        else:
            core = f"{s.a}{'+' if s.b > 0 else '-'}{abs(s.b)}{w}"
        return core if s.n == 1 else f"({core})/{s.n}"


ZZ = get_ring(1)
ZS2 = get_ring(2)
ZPHI = get_ring(5)


def from_json(R: Ring, v) -> El:
    if isinstance(v, int):
        return El(R, v)
    return El(R, *v)


# ------------------------------------------------------------- ring algebra

def divides(a: El, b: El) -> bool:
    """a | b in O (a != 0)."""
    return (b / a).is_integral()


def round_el(z: El) -> El:
    """A nearest element of O in the (1, w) coordinates: round(a/n) + round(b/n) w.

    For Z, Z[sqrt2], Z[phi] the fractional part f satisfies |N(f)| < 1, so this gives
    a norm-Euclidean division (|N(f)| <= 1/4 for phi, <= 1/2 for sqrt2)."""
    def rnd(x, n):  # round half up, exact
        return (2 * x + n) // (2 * n)
    return El(z.R, rnd(z.a, z.n), rnd(z.b, z.n), 1)


def ediv(a: El, b: El) -> Tuple[El, El]:
    q = round_el(a / b)
    return q, a - q * b


def egcd(a: El, b: El) -> Tuple[El, El, El]:
    """(g, x, y) with g = x a + y b a gcd of a and b."""
    R = a.R
    x0, y0, x1, y1 = R.one, R.zero, R.zero, R.one
    while not b.is_zero():
        q, r = ediv(a, b)
        a, b = b, r
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def gcd(a: El, b: El) -> El:
    if a.is_zero():
        return b
    if b.is_zero():
        return a
    return egcd(a, b)[0]


def gcd_list(xs: Iterable[El], R: Ring) -> El:
    g = R.zero
    for x in xs:
        if not x.is_zero():
            g = gcd(g, x)
    return g


def tp_normalise(z: El) -> El:
    """Canonical totally positive associate of z != 0 modulo unit squares.

    Multiply by +-1 and (if needed) by eps (norm -1, which flips the sigma-sign), then
    reduce by eta = eps^2 so that 1 <= z/sigma(z) < eta^2 at id."""
    R = z.R
    if z.is_zero():
        return z
    if z.sign() < 0:
        z = -z
    if R.D == 1:
        return z
    if z.ssign() < 0:
        z = z * R.eps
        if z.sign() < 0:
            z = -z
    eta = R.eta
    lim = eta * eta
    r = z / z.conj()
    while (r - 1).sign() < 0:
        z = z * eta
        r = z / z.conj()
    while (r - lim).sign() >= 0:
        z = z / eta
        r = z / z.conj()
    return z


def assoc_key(z: El) -> Tuple[int, int, int]:
    """Canonical key for the principal ideal (z), z != 0."""
    return tp_normalise(z).coords()


def ideal_eq(a: El, b: El) -> bool:
    return assoc_key(a) == assoc_key(b)


def unit_sqrt(w: El):
    """For a totally positive unit w, the unit e with e^2 = w and e > 0 at id."""
    R = w.R
    if not (w.is_unit() and w.tpos()):
        return None
    if w == R.one:
        return R.one
    if R.D == 1:
        return None
    # w = eta^k exactly; find k from the size at id
    e = R.one
    # walk eps^j both directions until e^2 = w
    for k in range(1, 400):
        e = e * R.eps
        if e * e == w:
            return e if e.sign() > 0 else -e
        ei = e.inv()
        if ei * ei == w:
            return ei if ei.sign() > 0 else -ei
    raise RuntimeError("unit_sqrt: exponent too large")


# ----------------------------------------------------------- factorisation

_FACT_CACHE: Dict[int, Dict[int, int]] = {}


def factor_int(n: int) -> Dict[int, int]:
    n = abs(int(n))
    if n in _FACT_CACHE:
        return dict(_FACT_CACHE[n])
    m, f, d = n, {}, 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        f[m] = f.get(m, 0) + 1
    _FACT_CACHE[n] = dict(f)
    return f


_PRIME_CACHE: Dict[Tuple[int, int], List[El]] = {}


def primes_above(p: int, R: Ring) -> List[El]:
    """Generators (canonical, totally positive) of the prime ideals above p."""
    key = (p, R.D)
    if key in _PRIME_CACHE:
        return _PRIME_CACHE[key]
    if R.D == 1:
        out = [R(p)]
    else:
        roots = [x for x in range(p) if (x * x - R.c1 * x - R.c0) % p == 0]
        if not roots:
            out = [R(p)]
        else:
            seen = {}
            for x in roots:
                g = tp_normalise(gcd(R(p), R.w - x))
                seen[g.coords()] = g
            out = list(seen.values())
    _PRIME_CACHE[key] = out
    return out


def factor(z: El) -> List[Tuple[El, int]]:
    """Prime ideal factorisation of (z), z in O nonzero: [(pi, e)], pi canonical."""
    assert z.is_integral() and not z.is_zero()
    out = []
    for p in sorted(factor_int(z.norm_num())):
        for q in primes_above(p, z.R):
            e, w = 0, z
            while divides(q, w):
                w = w / q
                e += 1
            if e:
                out.append((q, e))
    return out


def valuation(z: El, p: El) -> int:
    if z.is_zero():
        return 10 ** 9
    v = 0
    # handle non-integral z: v_p(z) = v_p(num) - v_p(den)
    if not z.is_integral():
        num = El(z.R, z.a, z.b, 1)
        return valuation(num, p) - valuation(z.R(z.n), p)
    while divides(p, z):
        z = z / p
        v += 1
    return v


_DIV_CACHE: Dict[Tuple[int, int, int, int], List[El]] = {}


def tp_divisors(z: El) -> List[El]:
    """Totally positive divisors of z modulo unit squares = ideal divisors of (z).

    Returned in canonical form, sorted by (norm, coords)."""
    key = (z.R.D,) + z.coords()
    if key not in _DIV_CACHE:
        R = z.R
        divs = [R.one]
        for q, e in factor(z):
            divs = [d * q ** k for d in divs for k in range(e + 1)]
        uniq = {}
        for d in divs:
            t = tp_normalise(d)
            uniq[t.coords()] = t
        _DIV_CACHE[key] = sorted(uniq.values(), key=lambda t: (abs(t.norm_num()), t.coords()))
    return list(_DIV_CACHE[key])


def is_squarefree(z: El) -> bool:
    if z.is_zero() or not z.is_integral():
        return False
    return all(e == 1 for _, e in factor(z))


def residues(d: El) -> List[El]:
    """A complete set of representatives of O/dO (d nonzero in O)."""
    R = d.R
    if R.D == 1:
        return [R(a) for a in range(abs(d.a))]
    # Z-lattice dO has basis d, d*w; HNF in coordinates (a, b)
    u, v = d, d * R.w
    a1, b1, a2, b2 = u.a, u.b, v.a, v.b
    q = igcd(b1, b2)
    n = abs(d.norm_num())
    p = n // q
    return [R(a, b) for a in range(p) for b in range(q)]
