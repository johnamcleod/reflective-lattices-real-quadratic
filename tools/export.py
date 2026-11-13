"""Final outputs: data/zphi_rank3.json (D=5) and data/zsqrt2_rank3.json (D=2).

    python tools/export.py D

Contents:
  candidates: every locally simple SSF candidate lattice (Gram matrix, det, status) with
    its certificate: the cyclic simple roots (reflective; check_polygon) or the
    translation certificate (non-reflective; check_nonreflective);
  classes: the isometry classes of the reflective ones: representative, Gram matrix,
    det, Coxeter polygon (angles pi/m_i in cyclic order and the simple roots), the
    members with an explicit phi (phi^T G_rep phi = G_member), and for D=2 the
    matching classes of Mark's appendix.
"""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "tools"))

from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.linalg import det  # noqa: E402
from zphi.vinberg import coxeter_m  # noqa: E402
from verify_all import final_records  # noqa: E402


def main():
    D = int(sys.argv[1])
    R = get_ring(D)
    fin = final_records(D)
    cands = []
    by_label = {}
    for (kind, key, li), r in sorted(fin.items()):
        G = [[from_json(R, x) for x in row] for row in r["gram"]]
        rec = {"kind": kind, "key": json.loads(key), "li": li, "gram": r["gram"],
               "det": det(G).to_json(), "status": r["status"]}
        if r["status"] == "reflective":
            rts = [[from_json(R, x) for x in v] for v in r["roots"]]
            n = len(rts)
            rec["polygon"] = {"roots": r["roots"],
                              "angles": [coxeter_m(G, rts[i], rts[(i + 1) % n]) for i in range(n)]}
        elif r["status"] == "nonreflective":
            rec["certificate"] = r["cert"]
        lab = f"{kind}|{key}|{li}"
        by_label[lab] = rec
        cands.append(rec)
    cl = json.load(open(os.path.join(ROOT, "data", f"cand_classes_{D}.json")))
    classes = []
    for c in cl["classes"]:
        ours = [x for x in c if not x.startswith("mark|")]
        if not ours:
            continue
        rep = ours[0]
        r = by_label[rep]
        classes.append({
            "representative": rep, "gram": r["gram"], "det": r["det"],
            "sides": len(r["polygon"]["angles"]), "polygon": r["polygon"],
            "members": [{"label": x, "phi": cl["certs"].get(x, {}).get("phi"),
                         "phi_from": cl["certs"].get(x, {}).get("rep")} for x in ours[1:]],
            "mark_classes": [x for x in c if x.startswith("mark|")]})
    classes.sort(key=lambda c: (c["sides"], c["polygon"]["angles"]))
    from collections import Counter
    out = {"ring": R.profile.name, "n_candidates": len(cands),
           "status": dict(Counter(c["status"] for c in cands)),
           "n_classes": len(classes),
           "classes_by_sides": dict(sorted(Counter(c["sides"] for c in classes).items())),
           "classes": classes, "candidates": cands}
    name = {5: "zphi_rank3.json", 2: "zsqrt2_rank3.json"}[D]
    json.dump(out, open(os.path.join(ROOT, "data", name), "w"))
    print(json.dumps({k: out[k] for k in ("ring", "n_candidates", "status", "n_classes",
                                          "classes_by_sides")}))


if __name__ == "__main__":
    main()
