"""The SSF lattices realising each of the twelve arithmetic triangles over Z[phi].

    python tools/triangle_lattices.py

For every short-edge triangle configuration (CC' a Coxeter value) and every SSF lattice
M in which its three roots are roots: compute the chamber of W(M) containing the
centroid of the triangle (chamber_search), certify it (check_polygon), and match it to
one of our classes (data/cand_classes_5.json) by an explicit isometry. Writes
data/triangles_5.json.
"""
import glob
import json
import os
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.run_lattices import records  # noqa: E402
from zphi.configs import build  # noqa: E402
from zphi.lattices import primitive_gram  # noqa: E402
from zphi.linalg import inv, mat_vec, gram_of, mat_mul, transpose, bil  # noqa: E402
from zphi.chamber import chamber_search  # noqa: E402
from zphi.vinberg import check_polygon, vertex_vector, coxeter_m  # noqa: E402
from zphi.isometry import find_isometry, invariant_key  # noqa: E402

R = get_ring(5)


def class_reps():
    data = json.load(open(os.path.join(ROOT, "data", "cand_classes_5.json")))
    want = {c[0] for c in data["classes"]}
    reps = {}
    for f in glob.glob(os.path.join(ROOT, "checkpoints", "cand", "5", "**", "*.jsonl"),
                       recursive=True):
        for line in open(f):
            r = json.loads(line)
            lab = f"{r['kind']}|{json.dumps(r['key'])}|{r['li']}"
            if r["status"] == "reflective" and lab in want and lab not in reps:
                reps[lab] = ([[from_json(R, x) for x in row] for row in r["gram"]],
                             [[from_json(R, x) for x in v] for v in r["roots"]])
    return reps


def main():
    g = {v: m for m, v in R.gammas.items()}
    reps = class_reps()
    keys = {lab: invariant_key(*reps[lab]) for lab in reps}
    out = []
    for rec in records(5, "short_edge"):
        key = tuple(from_json(R, x) for x in rec["key"])
        A, B, Ap, Bp, C, Cp = key
        cc = C * Cp
        if cc not in g or g[cc] == 2:
            continue
        cfg = build("short_edge", key)
        for li, L in enumerate(rec["lattices"]):
            Mb = [[from_json(R, x) for x in row] for row in L["basis"]]
            GM, _ = primitive_gram(gram_of(cfg.G, Mb))
            Minv = inv(Mb)
            rts = [mat_vec(Minv, x) for x in cfg.roots]
            ang = tuple(coxeter_m(GM, rts[i], rts[(i + 1) % 3]) for i in range(3))
            verts = [vertex_vector(GM, rts[i], rts[(i + 1) % 3]) for i in range(3)]
            # orient vertices into the triangle (negative on the opposite root)
            vs = []
            for i, v in enumerate(verts):
                opp = rts[(i + 2) % 3]
                vs.append([-c for c in v] if bil(GM, opp, v).sign() > 0 else v)
            # an interior point of the triangle on no mirror (any chamber inside the
            # triangle will do: W(M) is transitive on its chambers)
            res = None
            for w in ((1, 1, 1), (1, 2, 3), (3, 1, 2), (2, 5, 7), (7, 3, 11), (13, 5, 2)):
                c0 = [w[0] * vs[0][k] + w[1] * vs[1][k] + w[2] * vs[2][k] for k in range(3)]
                try:
                    res = chamber_search(GM, c0, max_hops=150)
                    break
                except ValueError as e:
                    if "mirror" not in str(e):
                        raise
            if res is None:
                raise RuntimeError("no interior point off the mirrors found")
            row = {"triangle": sorted(ang), "key": rec["key"], "li": li,
                   "locally_simple": L["locally_simple"], "status": res["status"]}
            if res["status"] == "closed":
                ch = check_polygon(GM, res["roots"])
                row["certified"] = ch["ok"]
                row["chamber_angles"] = ch["angles"]
                k = invariant_key(GM, res["roots"])
                row["class"] = None
                for lab, kk in keys.items():
                    if kk == k and find_isometry(GM, res["roots"], *reps[lab]) is not None:
                        row["class"] = lab
                        break
            out.append(row)
            print(json.dumps(row), flush=True)
    json.dump(out, open(os.path.join(ROOT, "data", "triangles_5.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
