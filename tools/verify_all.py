"""Re-verify every certificate of the candidate run with the current checkers.

    python tools/verify_all.py D [workers]

Final status per candidate = the last pass that decided it (checkpoints/cand/<D>/ then
pass2, pass3, ... in order). Reflective: check_polygon on the stored cyclic roots.
Non-reflective: check_nonreflective on the stored certificate. Writes
data/cand_final_<D>.json with the final status and the re-check result of every
locally simple candidate."""
import glob
import json
import os
import re
import sys
from collections import Counter
from multiprocessing import Pool

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.vinberg import check_polygon  # noqa: E402
from zphi.nonrefl import check_nonreflective  # noqa: E402

D = int(sys.argv[1]) if len(sys.argv) > 1 else 2


def final_records(D):
    ck = os.path.join(ROOT, "checkpoints", "cand", str(D))
    dirs = [ck] + sorted((d for d in glob.glob(os.path.join(ck, "pass*")) if os.path.isdir(d)),
                         key=lambda d: int(re.sub(r"\D", "", os.path.basename(d)) or 0))
    final = {}
    for d in dirs:
        for f in sorted(glob.glob(os.path.join(d, "*.jsonl"))):
            for line in open(f):
                r = json.loads(line)
                k = (r["kind"], json.dumps(r["key"]), r["li"])
                if k not in final or r["status"] in ("reflective", "nonreflective") \
                        or final[k]["status"] not in ("reflective", "nonreflective"):
                    final[k] = r
    return final


def check(r):
    R = get_ring(D)
    G = [[from_json(R, x) for x in row] for row in r["gram"]]
    st = r["status"]
    try:
        if st == "reflective":
            ok = check_polygon(G, [[from_json(R, x) for x in v] for v in r["roots"]])["ok"]
        elif st == "nonreflective":
            ok = check_nonreflective(G, r["cert"])["ok"]
        else:
            ok = None
    except Exception as ex:          # recorded, never hidden
        ok = f"exception {ex!r}"
    return {"kind": r["kind"], "key": r["key"], "li": r["li"], "status": st, "recheck": ok}


def main():
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else os.cpu_count()
    final = final_records(D)
    recs = list(final.values())
    with Pool(workers) as p:
        out = list(p.imap_unordered(check, recs, chunksize=1))
    summ = {"n": len(out), "status": dict(Counter(o["status"] for o in out)),
            "recheck": dict(Counter(f'{o["status"]}:{o["recheck"]}' for o in out))}
    json.dump({"summary": summ, "candidates": out},
              open(os.path.join(ROOT, "data", f"cand_final_{D}.json"), "w"))
    print(json.dumps(summ))


if __name__ == "__main__":
    main()
