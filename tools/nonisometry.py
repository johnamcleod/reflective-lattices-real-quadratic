"""Non-isometry certificates between the class representatives (exactness of the class count).

Two class representatives with different invariant_key (determinant ideal; cyclic
sequence of (root norm up to units, angle) up to dihedral symmetry) are not isometric.
For two representatives with the same key, find_isometry tries every dihedral alignment
of the certified chambers; by the alignment lemma (paper, Lemma lem:alignment) a failure
of all 2n alignments proves that they are not isometric. For each such pair this script
records, per alignment, why it fails, so that a checker can re-derive each failure:
  "norm"      some aligned norm ratio is not a unit square;
  "integral"  the solved phi is not in GL_3(O);
  "gram"      phi^T G2 phi != G1;
  "roots"     phi does not map every simple root to the aligned image.

    python3 tools/nonisometry.py D     -> data/nonisometry_D.json
"""
import json
import os
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import get_ring, from_json  # noqa: E402
from zphi.linalg import bil, det, inv, mat_mul, transpose, mat_vec, is_integral_mat  # noqa: E402
from zphi.isometry import invariant_key, find_isometry, _basis_matrix  # noqa: E402
from zphi.ring import unit_sqrt  # noqa: E402


def alignment_failures(G1, r1, G2, r2):
    """Per-alignment failure reasons (None if that alignment gives an isometry)."""
    n = len(r1)
    idx = next([(s + k) % n for k in range(3)] for s in range(n)
               if not det(_basis_matrix([r1[(s + k) % n] for k in range(3)])).is_zero())
    Ainv = inv(_basis_matrix([r1[i] for i in idx]))
    n1 = [bil(G1, r, r) for r in r1]
    n2 = [bil(G2, r, r) for r in r2]
    out = []
    for rev in (False, True):
        for k in range(n):
            perm = [((-i if rev else i) + k) % n for i in range(n)]
            imgs, why = [], None
            for i in range(n):
                q = n1[i] / n2[perm[i]]
                u = unit_sqrt(q) if q.is_unit() else None
                if u is None:
                    why = "norm"
                    break
                imgs.append([u * x for x in r2[perm[i]]])
            if why is None:
                phi = mat_mul(_basis_matrix([imgs[i] for i in idx]), Ainv)
                if not is_integral_mat(phi) or not det(phi).is_unit():
                    why = "integral"
                elif mat_mul(mat_mul(transpose(phi), G2), phi) != G1:
                    why = "gram"
                elif not all(mat_vec(phi, r1[i]) == imgs[i] for i in range(n)):
                    why = "roots"
            out.append({"rev": rev, "shift": k, "fails": why})
    return out


def main():
    D = int(sys.argv[1])
    R = get_ring(D)
    from zphi.fields import OUTPUT_NAMES
    name = OUTPUT_NAMES[D]
    data = json.load(open(os.path.join(ROOT, "data", name)))
    reps = []
    for c in data["classes"]:
        G = [[from_json(R, x) for x in row] for row in c["gram"]]
        rts = [[from_json(R, x) for x in v] for v in c["polygon"]["roots"]]
        reps.append((c["representative"], G, rts))
    buckets = defaultdict(list)
    for rep in reps:
        buckets[repr(invariant_key(rep[1], rep[2]))].append(rep)
    pairs = []
    for key, items in buckets.items():
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                (l1, G1, r1), (l2, G2, r2) = items[i], items[j]
                fails = alignment_failures(G1, r1, G2, r2)
                assert all(f["fails"] for f in fails), (l1, l2)
                assert find_isometry(G1, r1, G2, r2) is None
                pairs.append({"a": l1, "b": l2, "alignments": fails})
    out = {"ring": R.profile.name, "n_classes": len(reps), "n_buckets": len(buckets),
           "bucket_sizes": sorted((len(v) for v in buckets.values()), reverse=True),
           "n_pairs_same_key": len(pairs), "pairs": pairs}
    json.dump(out, open(os.path.join(ROOT, "data", f"nonisometry_{D}.json"), "w"))
    from collections import Counter
    print(json.dumps({k: out[k] for k in ("ring", "n_classes", "n_buckets", "n_pairs_same_key")}),
          "largest buckets", out["bucket_sizes"][:8],
          "failure kinds", dict(Counter(f["fails"] for p in pairs for f in p["alignments"])))


if __name__ == "__main__":
    main()
