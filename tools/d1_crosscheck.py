"""D1: cross-check AlVin's chambers of the reflective L_k = <-d, 1^(2+k)> over Z[phi]
(data/d1_roots_5.jsonl) against our own computations.

  k = 0:  our certified rank-3 chamber (data/diagonal_5.json, started at e0 with -e1+e2, -e2).
  k >= 1: our rank-n Vinberg (zphi/vinbergn.py, v0 = e0), normalised to AlVin's convention by
          a signed permutation of x_1..x_n (tools/d1_roots_ours.normalise).

The chamber at e0 is unique once the stabiliser walls are fixed (-e_i + e_{i+1}, -e_n), so
the two root sets must agree exactly. Results go to data/d1_crosscheck_5.jsonl (restartable:
(d, k) already present are skipped). Cases are run in order of k.

Roots over Z[phi] are determined by their mirrors only up to a unit (r and phi r give the same
reflection), so AlVin and our code may choose different representatives; `--summary`
compares the two chambers up to units (r ~ s iff s = u r with u a unit).

Usage: caffeinate -i nice -n 19 tools/memcap.sh 4000 .venv/bin/python tools/d1_crosscheck.py [time_limit]
       .venv/bin/python tools/d1_crosscheck.py --summary
"""
from __future__ import annotations

import json
import pathlib
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
from zphi.ring import get_ring  # noqa: E402
from zphi.vinbergn import vinberg_n  # noqa: E402
from d1_roots_ours import normalise  # noqa: E402

D = 5
OUT = ROOT / f"data/d1_crosscheck_{D}.jsonl"


def key(r):
    return tuple(tuple(x) for x in r)


def same_up_to_unit(R, r, s):
    """s = u r for a unit u of O."""
    r = [R(*x) for x in r]
    s = [R(*x) for x in s]
    i = next(j for j, x in enumerate(r) if not x.is_zero())
    if s[i].is_zero():
        return False
    u = s[i] / r[i]
    if not u.is_integral() or abs(u.norm_num()) != 1:
        return False
    return all((s[j] - u * r[j]).is_zero() for j in range(len(r)))


def summary():
    R = get_ring(D)
    rows = [json.loads(l) for l in open(OUT)]
    for r in rows:
        if r.get("status") != "reflective":
            print(r["d"], r["k"], r["status"])
            continue
        A, O = r["only_alvin"], r["only_ours"]
        match = len(A) == len(O) and all(sum(same_up_to_unit(R, a, o) for o in O) == 1 for a in A)
        r["agree_units"] = r["agree"] or match
        if not r["agree_units"]:
            print("DISAGREE", r["d"], r["k"], r["n_alvin"], r["n_ours"])
    ok = sum(1 for r in rows if r.get("agree_units"))
    print(f"{len(rows)} cases; agree up to units: {ok}; exact: {sum(1 for r in rows if r.get('agree'))}")


def main():
    if "--summary" in sys.argv:
        return summary()
    tl = float(sys.argv[1]) if len(sys.argv) > 1 else 3600
    R = get_ring(D)
    done = set()
    if OUT.exists():
        for l in open(OUT):
            r = json.loads(l)
            done.add((tuple(r["d"]), r["k"]))
    al = [json.loads(l) for l in open(ROOT / f"data/d1_roots_{D}.jsonl")]
    al.sort(key=lambda r: (r["k"], r["nroots"]))
    rk3 = {tuple(r["d"]): r for r in json.load(open(ROOT / f"data/diagonal_{D}.json"))["b"]}
    with open(OUT, "a") as f:
        for a in al:
            d, k = tuple(a["d"]), a["k"]
            if (d, k) in done:
                continue
            n = 3 + k
            G = [[(-R(*d) if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n)]
                 for i in range(n)]
            t0 = time.time()
            if k == 0:
                ours = [[R(*x) for x in r] for r in rk3[d]["roots"]]
                status, src = "reflective", f"data/diagonal_{D}.json"
            else:
                res = vinberg_n(G, [R.one] + [R.zero] * (n - 1), time_limit=tl)
                ours, status, src = res["roots"], res["status"], "vinbergn"
            rec = dict(D=D, d=list(d), k=k, status=status, src=src, secs=round(time.time() - t0, 1),
                       n_alvin=a["nroots"])
            if status == "reflective":
                nr, ok = normalise(R, [tuple(r) for r in ours])
                A = {key(r) for r in a["roots"]}
                O = {key([x.to_json() for x in r]) for r in nr}
                rec.update(normalised=ok, n_ours=len(O), agree=(A == O),
                           only_alvin=sorted(A - O), only_ours=sorted(O - A))
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps({x: rec.get(x) for x in ("d", "k", "status", "n_alvin", "n_ours", "agree", "secs")}),
                  flush=True)


if __name__ == "__main__":
    main()
