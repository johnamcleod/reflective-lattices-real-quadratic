"""D1: the chamber roots of every reflective L_k = <-d, 1^(2+k)> over Z[phi], from AlVin,
for the manuscript's root tables (tools/d1_tables.py).

AlVin's chamber convention (v0 = e0): the stabiliser walls are -e_i + e_{i+1} (1 <= i < n)
and -e_n (n = 2 + k), and every other wall has x_1 >= ... >= x_n >= 0. Padding a root of
L_k with zeros gives a vector of L_{k+1} in the same convention, so a root's set of
dimensions is well defined.

Writes data/d1_roots_5.jsonl: one record per reflective (d, k) with AlVin's roots (exact,
as [a, b] pairs, value a + b phi) and their norms; each root is re-checked to be a genuine
root ((r,r) totally positive, 2 (r, e_j)/(r, r) integral) as in tools/d1_rootcheck.py.

Usage: caffeinate -i nice -n 19 tools/memcap.sh 4000 .venv/bin/python tools/d1_roots.py 5
"""
from __future__ import annotations

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import d1_diagonal as DD  # noqa: E402
import alvin_crosscheck as AC  # noqa: E402
from zphi.ring import get_ring  # noqa: E402
from zphi.linalg import bil  # noqa: E402
from zphi.definite import is_root  # noqa: E402


def main():
    D = DD.D
    AC.D = D
    R = get_ring(D)
    recs = [json.loads(l) for l in open(ROOT / f"data/d1_diag_{D}.jsonl")]
    todo = [(tuple(r["d"]), r["k"]) for r in recs if not r.get("final") and r["status"] == "reflective"]
    out = ROOT / f"data/d1_roots_{D}.jsonl"
    with open(out, "w") as f:
        for d, k in todo:
            al = DD.run_alvin(d, k)
            n = 3 + k
            G = [[(-R(*d) if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n)]
                 for i in range(n)]
            roots = [[AC.parse_entry(t) for t in line] for line in al["root_lines"]]
            els = [[R(a, b) for a, b in r] for r in roots]
            rec = dict(D=D, d=list(d), k=k, ended=al["ended"], nroots=len(roots), roots=roots,
                       norms=[bil(G, r, r).to_json() for r in els],
                       genuine=all(is_root(G, r) for r in els))
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps({x: rec[x] for x in ("d", "k", "ended", "nroots", "genuine")}), flush=True)


if __name__ == "__main__":
    main()
