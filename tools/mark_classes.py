"""Isometry classes of the entries of Mark's appendix (expected: 432).

    python tools/mark_classes.py

Uses the chambers computed by tools/check_mark.py (data/mark_check.json, cycle order).
Writes data/mark_classes.json: classes (entry indices) and, for every entry that is
not a class representative, an explicit phi in GL_3(O) with phi^T G_rep phi = G_entry."""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import ZS2 as R, from_json  # noqa: E402
from zphi.isometry import classify  # noqa: E402
from zphi.linalg import mat_mul, transpose, det  # noqa: E402


def main():
    E = json.load(open(os.path.join(ROOT, "data", "mark_zsqrt2_432.json")))
    C = json.load(open(os.path.join(ROOT, "data", "mark_check.json")))["entries"]
    items, skipped = [], []
    for c in C:
        if c["vinberg"] != "reflective":
            skipped.append(c["idx"])
            continue
        G = [[from_json(R, x) for x in row] for row in E[c["idx"]]["gram"]]
        rts = [[from_json(R, x) for x in r] for r in c["roots"]]
        items.append((c["idx"], G, [rts[k] for k in c["cycle"]]))
    classes, certs = classify(items)
    Gs = {lab: G for lab, G, _ in items}
    for lab, (rep, phi) in certs.items():      # re-verify every certificate
        assert mat_mul(mat_mul(transpose(phi), Gs[rep]), phi) == Gs[lab]
        assert det(phi).is_unit()
    by_table = {}
    for cl in classes:
        t = tuple(sorted({E[i]["table"] for i in cl}))
        by_table[t] = by_table.get(t, 0) + 1
    out = {"n_entries": len(C), "skipped": skipped, "n_classes": len(classes),
           "class_sizes": sorted((len(c) for c in classes), reverse=True)[:20],
           "classes": classes,
           "certs": {str(k): {"rep": v[0], "phi": [[x.to_json() for x in row] for row in v[1]]}
                     for k, v in certs.items()},
           "tables_per_class": {"|".join(map(str, k)): v for k, v in by_table.items()}}
    json.dump(out, open(os.path.join(ROOT, "data", "mark_classes.json"), "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("n_entries", "skipped", "n_classes",
                                          "class_sizes", "tables_per_class")}))


if __name__ == "__main__":
    main()
