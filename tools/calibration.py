"""Gate A.3.5: the calibration lattices must occur among our reflective classes.

    python tools/calibration.py

For each calibration Gram matrix: run the chamber search from an interior point, certify
the chamber (check_polygon), then look for an explicit isometry phi (find_isometry,
phi^T G_rep phi = G_cal) to a representative of one of our classes
(data/cand_classes_5.json). Writes data/calibration_5.json.
"""
import json
import os
import sys
from fractions import Fraction as Fr

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.chamber import chamber_search  # noqa: E402
from zphi.vinberg import check_polygon  # noqa: E402
from zphi.isometry import find_isometry, invariant_key  # noqa: E402
from zphi.linalg import mat_mul, transpose, det  # noqa: E402

R = get_ring(5)
phi = R(0, 1)
sqrt5 = R(-1, 2)

CAL = [   # (name, diagonal, source)
    ("<-phi,1,1>", [-phi, R(1), R(1)], "Bugaenko"),
    ("<-sqrt5,1,1>", [-sqrt5, R(1), R(1)], "Guglielmetti thesis 2017"),
    ("<-(3+2sqrt5),1,1>", [-(3 + 2 * sqrt5), R(1), R(1)], "Mcleod thesis 2013, 3.2"),
    ("<-(-3+2sqrt5),1,1>", [-(-3 + 2 * sqrt5), R(1), R(1)], "Mcleod thesis 2013, 3.2"),
    ("<-phi,2+phi,1>", [-phi, 2 + phi, R(1)], "Guglielmetti"),
]


def diag(d):
    return [[d[i] if i == j else R(0) for j in range(3)] for i in range(3)]


def load_reps():
    data = json.load(open(os.path.join(ROOT, "data", "cand_classes_5.json")))
    want = {c[0] for c in data["classes"]}
    reps = {}
    import glob
    for f in glob.glob(os.path.join(ROOT, "checkpoints", "cand", "5", "**", "*.jsonl"),
                       recursive=True):
        for line in open(f):
            r = json.loads(line)
            lab = f"{r['kind']}|{json.dumps(r['key'])}|{r['li']}"
            if r["status"] == "reflective" and lab in want and lab not in reps:
                G = [[from_json(R, x) for x in row] for row in r["gram"]]
                rts = [[from_json(R, x) for x in v] for v in r["roots"]]
                reps[lab] = (G, rts)
    return reps


def main():
    reps = load_reps()
    out = []
    for name, d, src in CAL:
        G = diag(d)
        v0 = [R(1), R(1, 0, 7), R(1, 0, 11)]     # timelike (|d| > 1/49 + 1/121), generic
        res = chamber_search(G, v0)
        rec = {"name": name, "source": src, "det": str(det(G)), "status": res["status"]}
        if res["status"] != "closed":
            out.append(rec)
            print(json.dumps(rec), flush=True)
            continue
        roots = res["roots"]
        chk = check_polygon(G, roots)
        rec["certified"] = chk["ok"]
        rec["angles"] = chk["angles"]
        key = invariant_key(G, roots)
        rec["match"] = None
        for lab, (G2, r2) in reps.items():
            if invariant_key(G2, r2) != key:
                continue
            P = find_isometry(G, roots, G2, r2)
            if P is not None:
                assert mat_mul(mat_mul(transpose(P), G2), P) == G
                rec["match"] = lab
                rec["phi"] = [[x.to_json() for x in row] for row in P]
                break
        out.append(rec)
        print(json.dumps({k: rec[k] for k in rec if k != "phi"}), flush=True)
    json.dump(out, open(os.path.join(ROOT, "data", "calibration_5.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
