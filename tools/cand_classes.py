"""Isometry classes of the reflective candidates (gate A.3.4) and their match with
Mark's appendix classes.

    python tools/cand_classes.py D

Items: every candidate with status "reflective" in checkpoints/cand/<D>/ (all passes),
together with one representative per Mark class (data/mark_classes.json). Classified
jointly by zphi.isometry.classify, so each of our classes is either merged with a Mark
class by an explicit phi or shown to be distinct (different invariant, or a complete
chamber-alignment search failed). Every phi is re-verified. Writes
data/cand_classes_<D>.json."""
import glob
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.isometry import classify  # noqa: E402
from zphi.linalg import mat_mul, transpose, det  # noqa: E402
from zphi.vinberg import check_polygon  # noqa: E402


def main():
    D = int(sys.argv[1])
    R = get_ring(D)
    items, recheck_fail = [], []
    for f in sorted(glob.glob(os.path.join(ROOT, "checkpoints", "cand", str(D), "**", "*.jsonl"),
                         recursive=True)):
        for line in open(f):
            r = json.loads(line)
            if r["status"] != "reflective":
                continue
            G = [[from_json(R, x) for x in row] for row in r["gram"]]
            rts = [[from_json(R, x) for x in v] for v in r["roots"]]
            if not check_polygon(G, rts)["ok"]:     # re-check with the current checker
                recheck_fail.append([r["kind"], r["key"], r["li"]])
                continue
            lab = f"{r['kind']}|{json.dumps(r['key'])}|{r['li']}"
            items.append((lab, G, rts))
    seen = {it[0] for it in items}
    items = [it for i, it in enumerate(items) if it[0] not in {x[0] for x in items[:i]}] \
        if len(seen) != len(items) else items
    n_ours = len(items)
    if D == 2:
        E = json.load(open(os.path.join(ROOT, "data", "mark_zsqrt2_432.json")))
        C = {c["idx"]: c for c in json.load(open(os.path.join(ROOT, "data", "mark_check.json")))["entries"]}
        MC = json.load(open(os.path.join(ROOT, "data", "mark_classes.json")))
        for cl in MC["classes"]:
            c = C[cl[0]]
            G = [[from_json(R, x) for x in row] for row in E[c["idx"]]["gram"]]
            rts = [[from_json(R, x) for x in v] for v in c["roots"]]
            # Mark reps first in their bucket, so they become the class representatives
            items.insert(0, (f"mark|{cl[0]}", G, [rts[k] for k in c["cycle"]]))
    classes, certs = classify(items)
    Gs = {lab: G for lab, G, _ in items}
    for lab, (rep, phi) in certs.items():
        assert mat_mul(mat_mul(transpose(phi), Gs[rep]), phi) == Gs[lab]
        assert det(phi).is_unit()
    ours = [c for c in classes if any(not x.startswith("mark|") for x in c)]
    mark_only = [c for c in classes if all(x.startswith("mark|") for x in c)]
    new = [c for c in classes if not any(x.startswith("mark|") for x in c)]
    out = {"n_reflective": n_ours, "recheck_fail": recheck_fail,
           "n_classes_ours": len(ours), "n_mark_classes_not_found": len(mark_only),
           "n_new_classes": len(new), "new_classes": new, "classes": classes,
           "certs": {k: {"rep": v[0], "phi": [[x.to_json() for x in row] for row in v[1]]}
                     for k, v in certs.items()}}
    json.dump(out, open(os.path.join(ROOT, "data", f"cand_classes_{D}.json"), "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("n_reflective", "recheck_fail", "n_classes_ours",
                                          "n_mark_classes_not_found", "n_new_classes",
                                          "new_classes")}))


if __name__ == "__main__":
    main()
