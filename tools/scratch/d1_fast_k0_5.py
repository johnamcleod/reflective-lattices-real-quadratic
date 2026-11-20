"""Rerun the three Z[phi] k=0 cases that hit Delta_max = 1e6 in d1_fast (cap 1e12)."""
import json, sys, time, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(ROOT / "tools"))
from zphi.ring import get_ring
from zphi.vinbergdiag import vinberg_diag
from d1_fast import compare
R = get_ring(5)
ours = {tuple(r["d"]): r["roots"] for r in json.load(open(ROOT / "data/diagonal_5.json"))["b"] if r["status"] == "reflective"}
for d in [(-8, 10), (-7, 8), (-4, 17)]:
    t0 = time.time()
    res = vinberg_diag(R(*d), 2, time_limit=3600, Delta_max=10 ** 12)
    print(json.dumps(dict(d=d, status=res["status"], reason=res.get("reason"), nroots=len(res["roots"]),
                          Delta=str(res["Delta"]), ours=compare(R, res["roots"], ours.get(d)) if res["status"] == "reflective" else None,
                          secs=round(time.time() - t0, 1))), flush=True)
