"""PARI cross-checks (tests only). Elements are passed in the integral basis
[1, x] of nfinit(x^2-2) / nfinit(x^2-x-1), which is (1, w)."""
import cypari2

pari = cypari2.Pari()
_NF = {}


def nf(R):
    if R.D not in _NF:
        _NF[R.D] = pari.nfinit({1: "y", 2: "y^2-2", 5: "y^2-y-1"}[R.D])
    return _NF[R.D]


def to_pari(z):
    if z.R.D == 1:
        return pari(f"{z.a}/{z.n}")
    return pari(f"[{z.a}/{z.n}, {z.b}/{z.n}]~")


def mat_to_pari(M):
    n, m = len(M), len(M[0])
    P = pari.matrix(n, m)
    for i in range(n):
        for j in range(m):
            P[i, j] = to_pari(M[i][j])
    return P


def ideal(R, z):
    return pari.idealhnf(nf(R), to_pari(z))
