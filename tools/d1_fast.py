"""D1 with the diagonal fast path (zphi/vinbergdiag.py): the chamber of every reflective
L_k = <-d, 1^(2+k)> (both fields), compared up to units with AlVin (data/d1_roots_{D}.jsonl)
and with our earlier chambers (data/d1_roots_ours.jsonl: certified rank-3 chambers and
generic stage-2 runs), and one step further: the first k at which AlVin did not end
(the "open" step), with a time limit.

Records go to data/d1_fast_{D}.jsonl, one per (d, k), with
  role:   "known" (a reflective step from the AlVin runs, or k = 0 of a form reflective in
          rank 3) or "open" (the first step beyond);
  status: reflective | undetermined (time limit / Delta_max) | not_b_n (stabiliser is not
          B_n; use vinbergn);
  alvin, ours: "same" | "units" | "differs" | null (no chamber to compare).

Usage: caffeinate -i nice -n 19 tools/memcap.sh 4000 .venv/bin/python tools/d1_fast.py D [time_limit]
"""
from __future__ import annotations

import json
import pathlib
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from zphi.ring import get_ring  # noqa: E402
from zphi.linalg import bil  # noqa: E402
from zphi.vinbergdiag import vinberg_diag  # noqa: E402


def same_up_to_unit(R, r, s):
    i = next(j for j, x in enumerate(r) if not x.is_zero())
    if s[i].is_zero():
        return False
    u = s[i] / r[i]
    if not u.is_integral() or abs(u.norm_num()) != 1:
        return False
    return all((s[j] - u * r[j]).is_zero() for j in range(len(r)))


def compare(R, ours, other):
    if other is None:
        return None
    A = {tuple(tuple(x.to_json()) for x in r) for r in ours}
    B = {tuple(tuple(x) for x in r) for r in other}
    if A == B:
        return "same"
    o = [[R(*x) for x in r] for r in other]
    if len(ours) == len(o) and all(sum(same_up_to_unit(R, r, s) for s in o) == 1 for r in ours):
        return "units"
    return "differs"


def main():
    D = int(sys.argv[1])
    tl = float(sys.argv[2]) if len(sys.argv) > 2 else 3600
    R = get_ring(D)
    out = ROOT / f"data/d1_fast_{D}.jsonl"
    done = set()
    if out.exists():
        for l in open(out):
            r = json.loads(l)
            done.add((tuple(r["d"]), r["k"]))
    al = {}
    p = ROOT / f"data/d1_roots_{D}.jsonl"
    for l in open(p):
        r = json.loads(l)
        if r["ended"]:
            al[(tuple(r["d"]), r["k"])] = r["roots"]
    ours = {}
    for l in open(ROOT / "data/d1_roots_ours.jsonl"):
        r = json.loads(l)
        if r["D"] == D and r.get("status") == "reflective":
            ours[(tuple(r["d"]), r["k"])] = r["roots"]
    refl3 = {tuple(r["d"]) for r in json.load(open(ROOT / f"data/diagonal_{D}.json"))["b"]
             if r["status"] == "reflective"}
    cases = []
    for l in open(ROOT / f"data/d1_diag_{D}.jsonl"):
        r = json.loads(l)
        if not r.get("final") or tuple(r["d"]) not in refl3:
            continue
        d = tuple(r["d"])
        ka = r["k_reflective_max"] if r["k_reflective_max"] is not None else 0
        cases += [(d, k, "known") for k in range(ka + 1)] + [(d, ka + 1, "open")]
    cases.sort(key=lambda c: (c[1], c[0]))
    with open(out, "a") as f:
        for d, k, role in cases:
            if (d, k) in done:
                continue
            t0 = time.time()
            rec = dict(D=D, d=list(d), k=k, role=role)
            try:
                res = vinberg_diag(R(*d), 2 + k, time_limit=tl)
            except ValueError as e:
                rec.update(status="not_b_n", reason=str(e))
            else:
                rec.update(status=res["status"], reason=res.get("reason"), nroots=len(res["roots"]),
                           roots=[[x.to_json() for x in r] for r in res["roots"]],
                           norms=[bil([[(-R(*d) if i == j == 0 else (R.one if i == j else R.zero))
                                        for j in range(3 + k)] for i in range(3 + k)], r, r).to_json()
                                  for r in res["roots"]],
                           coxiter=res.get("coxiter"))
                if res["status"] == "reflective":
                    rec.update(alvin=compare(R, res["roots"], al.get((d, k))),
                               ours=compare(R, res["roots"], ours.get((d, k))))
            rec["secs"] = round(time.time() - t0, 1)
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps({x: rec.get(x) for x in ("d", "k", "role", "status", "nroots", "alvin", "ours", "secs")}),
                  flush=True)


if __name__ == "__main__":
    main()
