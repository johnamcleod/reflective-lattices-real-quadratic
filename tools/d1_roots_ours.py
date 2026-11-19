"""D1: chamber roots from our own Vinberg (zphi/vinbergn.py, v0 = e0), for the forms where
AlVin is not usable: over Q(sqrt13) (AlVin may return a reflection subgroup's polytope,
DISCREPANCIES #7) every reflective step; over Z[phi] the k = 0 step of the forms AlVin does
not finish in rank 3.

Each chamber is brought into AlVin's convention (stabiliser walls -e_i + e_{i+1}, -e_n) by
a signed permutation of x_1..x_n (an isometry fixing e0, so the chamber stays the one at
e0). Records that cannot be so normalised are kept with normalised = false.

Appends to data/d1_roots_ours.jsonl (restartable: (D, d, k) already present are skipped).
Reuses logs/vn13.jsonl (Q(sqrt13), k >= 1) when present.

Usage: caffeinate -i nice -n 19 tools/memcap.sh 4000 .venv/bin/python tools/d1_roots_ours.py
"""
from __future__ import annotations

import itertools
import json
import pathlib
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from zphi.ring import get_ring  # noqa: E402
from zphi.linalg import bil  # noqa: E402
from zphi.definite import is_root  # noqa: E402
from zphi.vinbergn import vinberg_n  # noqa: E402

OUT = ROOT / "data/d1_roots_ours.jsonl"
# Cases our implementation does not finish in reasonable time (stopped, not refuted).
SKIP = {(13, (-2, 1), 2): "stage-2 run stopped after 2.5 h in one enumeration batch (2026-11-19)"}


def standard_stab(R, n):
    out = []
    m = n - 1  # number of space coordinates
    for i in range(1, m):
        v = [R.zero] * n
        v[i], v[i + 1] = -R.one, R.one
        out.append(tuple(v))
    v = [R.zero] * n
    v[m] = -R.one
    out.append(tuple(v))
    return set(out)


def normalise(R, roots):
    n = len(roots[0])
    m = n - 1
    target = standard_stab(R, n)
    for perm in itertools.permutations(range(1, n)):
        for signs in itertools.product((1, -1), repeat=m):
            def g(r):
                return tuple([r[0]] + [signs[t] * r[perm[t]] for t in range(m)])
            img = [g(r) for r in roots]
            if target <= set(img):
                return [list(r) for r in img], True
    return roots, False


def cases():
    out = []
    for D in (5, 13):
        fin = [json.loads(l) for l in open(ROOT / f"data/d1_diag_{D}.jsonl")]
        fin = [r for r in fin if r.get("final")]
        refl = {tuple(r["d"]) for r in json.load(open(ROOT / f"data/diagonal_{D}.json"))["b"]
                if r["status"] == "reflective"}
        for r in fin:
            d = tuple(r["d"])
            if d not in refl:
                continue
            if D == 13:
                for k in range(0, (r["k_reflective_max"] if r["k_reflective_max"] is not None else 0) + 1):
                    out.append((D, d, k))
            elif r["k_reflective_max"] is None:
                out.append((D, d, 0))
    return out


def main():
    done = set()
    if OUT.exists():
        for l in open(OUT):
            r = json.loads(l)
            done.add((r["D"], tuple(r["d"]), r["k"]))
    vn13 = {}
    p = ROOT / "logs/vn13.jsonl"
    if p.exists():
        for l in open(p):
            r = json.loads(l)
            vn13[(tuple(r["d"]), r["k"])] = r
    with open(OUT, "a") as f:
        for D, d, k in cases():
            if (D, d, k) in done:
                continue
            R = get_ring(D)
            n = 3 + k
            G = [[(-R(*d) if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n)]
                 for i in range(n)]
            t0 = time.time()
            if D == 13 and (d, k) in vn13:
                v = vn13[(d, k)]
                roots = [[R(*x) for x in r] for r in v["roots"]]
                status, src = v["status"], "logs/vn13.jsonl"
            elif (D, d, k) in SKIP:
                rec = dict(D=D, d=list(d), k=k, status="skipped", src=SKIP[(D, d, k)])
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print(json.dumps(rec), flush=True)
                continue
            else:
                res = vinberg_n(G, [R.one] + [R.zero] * (n - 1), time_limit=3600)
                roots, status, src = res["roots"], res["status"], "vinbergn"
            rec = dict(D=D, d=list(d), k=k, status=status, src=src, secs=round(time.time() - t0, 1))
            if status == "reflective":
                nr, ok = normalise(R, [tuple(r) for r in roots])
                rec.update(normalised=ok, nroots=len(nr),
                           roots=[[x.to_json() for x in r] for r in nr],
                           norms=[bil(G, list(r), list(r)).to_json() for r in nr],
                           genuine=all(is_root(G, list(r)) for r in nr))
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps({x: rec.get(x) for x in ("D", "d", "k", "status", "nroots", "normalised", "genuine", "secs")}), flush=True)


if __name__ == "__main__":
    main()
