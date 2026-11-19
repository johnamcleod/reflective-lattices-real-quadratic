"""D1: every root AlVin returns for a reflective L_k = <-d, 1^(2+k)> must be a genuine root
of the lattice: (r, r) totally positive and 2 (r, e_j) / (r, r) in O for every basis vector
e_j (so the reflection in r is integral). Then the polytope AlVin returns, bounded by real
mirrors and of finite volume (CoxIter), proves L_k reflective even if AlVin missed roots
(DISCREPANCIES #7: over Q(sqrt 13) it can). Exact arithmetic.

Usage: caffeinate -i nice -n 19 tools/memcap.sh 2000 .venv/bin/python tools/d1_rootcheck.py D
  -> data/d1_rootcheck_{D}.jsonl
"""
import json
import pathlib
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = int(sys.argv[1])
sys.argv = [sys.argv[0], f"--D={D}"]
sys.path.insert(0, str(ROOT / "tools"))
import alvin_crosscheck as AC  # noqa: E402
import d1_diagonal as D1  # noqa: E402

AC.D = D1.D = D
c0, c1 = AC._C0C1[D]


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def tot_pos(x):
    """x = a + b w > 0 under both embeddings (exact: sign of a + b w via squares)."""
    a, b = x
    disc = c1 * c1 + 4 * c0  # w = (c1 + sqrt disc)/2
    def pos(sgn):  # a + b (c1 + sgn sqrt disc)/2 > 0  <=>  2a + b c1 + sgn b sqrt disc > 0
        u, v = 2 * a + b * c1, sgn * b
        if u >= 0 and v >= 0:
            return u > 0 or v > 0
        if u <= 0 and v <= 0:
            return False
        return (u * u > v * v * disc) if u > 0 else (v * v * disc > u * u)
    return pos(1) and pos(-1)


def integral(q):
    return q[0].denominator == 1 and q[1].denominator == 1


def check(d, k):
    al = D1.run_alvin(tuple(d), k)
    g = [(-d[0], -d[1])] + [(1, 0)] * (2 + k)  # Gram diag(-d, 1, ..., 1)
    roots = [[AC.parse_entry(t) for t in line] for line in al["root_lines"]]
    bad = []
    for r in roots:
        rr = (0, 0)
        for x, gi in zip(r, g):
            rr = add(rr, AC.mul(gi, AC.mul(x, x)))
        ok = tot_pos(rr) and all(
            integral(AC.div(AC.mul((2, 0), AC.mul(x, gi)), rr)) for x, gi in zip(r, g))
        if not ok:
            bad.append(r)
    return dict(D=D, d=d, k=k, ended=al["ended"], nroots=len(roots), all_genuine=not bad,
                bad=bad)


def main():
    recs = [json.loads(l) for l in open(ROOT / f"data/d1_diag_{D}.jsonl")]
    todo = [(r["d"], r["k"]) for r in recs if not r.get("final") and r["status"] == "reflective"]
    with open(ROOT / f"data/d1_rootcheck_{D}.jsonl", "w") as f:
        for d, k in todo:
            rec = check(d, k)
            f.write(json.dumps(rec) + "\n")
            f.flush()
    out = [json.loads(l) for l in open(ROOT / f"data/d1_rootcheck_{D}.jsonl")]
    print(json.dumps(dict(D=D, runs=len(out), ended=sum(r["ended"] for r in out),
                          all_genuine=sum(r["all_genuine"] for r in out),
                          bad=[(r["d"], r["k"]) for r in out if not r["all_genuine"]])))


if __name__ == "__main__":
    main()
