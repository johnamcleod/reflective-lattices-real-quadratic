"""Exact arithmetic for O = Z, Z[sqrt2], Z[phi] (field K = Q, Q(sqrt2), Q(sqrt5)).

Elements are x + y*sqrt(D) with Fraction coefficients. D = 1 means K = Q (y = 0).
id: sqrt(D) > 0;  sigma: sqrt(D) -> -sqrt(D) (trivial when D = 1).
All comparisons are exact. Each ring here has a fundamental unit of norm -1, so
the totally positive units are exactly the squares of units (Mark's (U2)).
"""
from fractions import Fraction as Fr
from math import isqrt, sqrt


class Ring:
    def __init__(self, D):
        assert D in (1, 2, 5)
        self.D = D
        self.name = {1: "Z", 2: "Z[sqrt2]", 5: "Z[phi]"}[D]
        if D == 1:
            self.omega = None
            self.eps = self(1)            # no non-trivial units beyond -1
        elif D == 2:
            self.omega = self(0, 1)        # sqrt2
            self.eps = self(1, 1)          # 1 + sqrt2, norm -1
        else:
            self.omega = self(Fr(1, 2), Fr(1, 2))   # phi
            self.eps = self.omega
        self.eta = self.eps * self.eps     # fundamental totally positive unit

    def __call__(self, x, y=0):
        return El(self, x, y)

    def from_basis(self, a, b):
        """a + b*omega."""
        if self.D == 1:
            return self(a)
        return self(a) + b * self.omega

    def basis_coords(self, z):
        if self.D == 1:
            return (z.x, Fr(0))
        if self.D == 2:
            return (z.x, z.y)
        return (z.x - z.y, 2 * z.y)   # phi-basis

    def elements_in_box(self, lo, hi, slo=None, shi=None):
        """All z in O with lo < z < hi and (if D>1) slo < sigma(z) < shi, exactly.

        Bounds may be ints, Fractions, El's or floats (floats are used as given)."""
        def ex(v):
            return v if isinstance(v, El) else self(Fr(v))
        Lo, Hi = ex(lo), ex(hi)
        flo, fhi = float(Lo), float(Hi)
        if self.D == 1:
            return [self(n) for n in range(int(flo) - 1, int(fhi) + 2)
                    if (self(n) - Lo).sign() > 0 and (Hi - self(n)).sign() > 0]
        SLo, SHi = ex(slo), ex(shi)
        fslo, fshi = float(SLo), float(SHi)
        w = float(self.omega)
        ws = float(self.omega.conj())
        out = []
        bmin = int((flo - fshi) / (w - ws)) - 2
        bmax = int((fhi - fslo) / (w - ws)) + 2
        for b in range(bmin, bmax + 1):
            amin = int(min(flo - b * w, fslo - b * ws)) - 2
            amax = int(max(fhi - b * w, fshi - b * ws)) + 2
            for a in range(amin, amax + 1):
                zf, zs = a + b * w, a + b * ws
                if flo - 1e-6 < zf < fhi + 1e-6 and fslo - 1e-6 < zs < fshi + 1e-6:
                    z = self.from_basis(a, b)
                    if ((z - Lo).sign() > 0 and (Hi - z).sign() > 0
                            and (z - SLo).ssign() > 0 and (SHi - z).ssign() > 0):
                        out.append(z)
        return out


class El:
    __slots__ = ("R", "x", "y")

    def __init__(self, R, x, y=0):
        self.R = R
        self.x = Fr(x)
        self.y = Fr(y) if R.D != 1 else Fr(0)

    def _c(self, o):
        return o if isinstance(o, El) else El(self.R, o)

    def __add__(s, o):
        o = s._c(o); return El(s.R, s.x + o.x, s.y + o.y)
    __radd__ = __add__

    def __sub__(s, o):
        o = s._c(o); return El(s.R, s.x - o.x, s.y - o.y)

    def __rsub__(s, o):
        return s._c(o) - s

    def __neg__(s):
        return El(s.R, -s.x, -s.y)

    def __mul__(s, o):
        o = s._c(o); D = s.R.D
        return El(s.R, s.x * o.x + D * s.y * o.y, s.x * o.y + s.y * o.x)
    __rmul__ = __mul__

    def conj(s):
        return El(s.R, s.x, -s.y)

    def norm(s):
        return s.x * s.x - s.R.D * s.y * s.y

    def inv(s):
        n = s.norm()
        if n == 0:
            raise ZeroDivisionError
        return El(s.R, s.x / n, -s.y / n)

    def __truediv__(s, o):
        return s * s._c(o).inv()

    def __rtruediv__(s, o):
        return s._c(o) * s.inv()

    def __pow__(s, k):
        r = El(s.R, 1)
        b = s if k >= 0 else s.inv()
        for _ in range(abs(k)):
            r = r * b
        return r

    def __eq__(s, o):
        o = s._c(o); return s.x == o.x and s.y == o.y

    def __hash__(s):
        return hash((s.x, s.y))

    def is_zero(s):
        return s.x == 0 and s.y == 0

    def sign(s):
        x, y, D = s.x, s.y, s.R.D
        if y == 0:
            return (x > 0) - (x < 0)
        if x >= 0 and y >= 0:
            return 1
        if x <= 0 and y <= 0:
            return -1
        d = x * x - D * y * y
        if d == 0:
            return 0
        return (1 if x > 0 else -1) if d > 0 else (1 if y > 0 else -1)

    def ssign(s):
        return s.conj().sign()

    def tpos(s):
        if s.R.D == 1:
            return s.sign() > 0
        return s.sign() > 0 and s.ssign() > 0

    def is_integral(s):
        D = s.R.D
        if D in (1, 2):
            return s.x.denominator == 1 and s.y.denominator == 1
        a, b = 2 * s.x, 2 * s.y
        return a.denominator == 1 and b.denominator == 1 and (a - b) % 2 == 0

    def is_unit(s):
        return (not s.is_zero()) and s.is_integral() and abs(s.norm()) == 1

    def __float__(s):
        return float(s.x) + float(s.y) * sqrt(s.R.D) if s.R.D != 1 else float(s.x)

    def sfloat(s):
        return float(s.conj())

    def __repr__(s):
        R = s.R
        if R.D == 1:
            return str(s.x)
        if s.is_integral():
            a, b = R.basis_coords(s)
            w = "√2" if R.D == 2 else "φ"
            if b == 0:
                return f"{a}"
            if a == 0:
                return f"{b}{w}"
            return f"{a}{'+' if b > 0 else '-'}{abs(b)}{w}"
        return f"({s.x}+{s.y}√{R.D})"


# ---------------------------------------------------------------- ring algebra

def divides(a, b):
    return (b / a).is_integral()


def round_el(z):
    """Nearest element of O to z (in the omega-basis); norm-Euclidean for D=1,2,5."""
    R = z.R
    a, b = R.basis_coords(z)
    return R.from_basis(round(a), round(b))


def ediv(a, b):
    q = round_el(a / b)
    return q, a - q * b


def egcd(a, b):
    """Return (g, x, y) with g = x a + y b a gcd of a, b."""
    R = a.R
    x0, y0, x1, y1 = R(1), R(0), R(0), R(1)
    while not b.is_zero():
        q, r = ediv(a, b)
        a, b = b, r
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def gcd(a, b):
    if a.is_zero():
        return b
    if b.is_zero():
        return a
    return egcd(a, b)[0]


def tp_normalise(z):
    """Multiply z by a unit to make it totally positive (z != 0), and reduce
    modulo unit squares to a canonical representative."""
    R = z.R
    if z.is_zero():
        return z
    if z.sign() < 0:
        z = -z
    if R.D != 1:
        if z.ssign() < 0:
            z = z * R.eps if R.eps.sign() > 0 else -z * R.eps
            if z.sign() < 0:
                z = -z
        assert z.tpos()
        # reduce: 1 <= z / sigma z < eta^2
        eta = R.eta
        lim = eta * eta
        r = z / z.conj()
        while (r - 1).sign() < 0:
            z = z * eta; r = z / z.conj()
        while (r - lim).sign() >= 0:
            z = z / eta; r = z / z.conj()
    return z


def assoc_key(z):
    """Canonical key for the ideal (z), z != 0."""
    w = tp_normalise(z)
    return (w.x, w.y)


_div_cache = {}


def tp_divisors(z):
    """Totally positive divisors of z modulo unit squares (= ideal divisors of (z))."""
    key = (z.R.D, z.x, z.y)
    if key not in _div_cache:
        _div_cache[key] = _tp_divisors(z)
    return list(_div_cache[key])


def _tp_divisors(z):
    R = z.R
    if R.D == 1:
        n = abs(int(z.x))
        return [R(d) for d in range(1, n + 1) if n % d == 0]
    nz = z.norm()
    assert nz.denominator == 1
    fac = []
    for p in factor_int(nz):
        for q in primes_above(p, R):
            e, w = 0, z
            while divides(q, w):
                w = w / q
                e += 1
            if e:
                fac.append((q, e))
    divs = [R(1)]
    for q, e in fac:
        divs = [d * q ** k for d in divs for k in range(e + 1)]
    out = {}
    for d in divs:
        out[assoc_key(d)] = tp_normalise(d)
    return list(out.values())


_prime_cache = {}


def primes_above(p, R):
    """Generators of the prime ideals of O above the rational prime p."""
    key = (p, R.D)
    if key in _prime_cache:
        return _prime_cache[key]
    if R.D == 1:
        out = [R(p)]
    else:
        # minimal polynomial of omega: x^2 - 2 (D=2) or x^2 - x - 1 (D=5)
        f = (lambda x: (x * x - 2) % p) if R.D == 2 else (lambda x: (x * x - x - 1) % p)
        roots = [x for x in range(p) if f(x) == 0]
        if not roots:
            out = [R(p)]                       # inert
        else:
            out = {}
            for x in roots:
                g = gcd(R(p), R.omega - x)
                out[assoc_key(g)] = g
            out = list(out.values())
    _prime_cache[key] = out
    return out


def factor_int(n):
    n = abs(int(n))
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def is_squarefree(z):
    if z.is_zero():
        return False
    N = z.norm()
    assert N.denominator == 1
    for p in factor_int(N):
        for q in primes_above(p, z.R):
            if divides(q * q, z):
                return False
    return True


def ideal_eq(a, b):
    return assoc_key(a) == assoc_key(b)
