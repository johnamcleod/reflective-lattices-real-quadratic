"""Gate A.3.6: the Z[phi] lattices with a pi/4 corner are exactly the reflective <-d,1,1>.

    python tools/diagonal_check.py [NMAX] [workers]

(a) Every reflective class (data/cand_classes_5.json) whose chamber has an angle pi/4 is
    isometric to <det,1,1>: the chamber of the diagonal lattice is computed and
    certified, and an explicit phi with phi^T G_rep phi = G_diag is found.
(b) Every SSF admissible <-d,1,1> with |N(d)| <= NMAX is run (chamber search, then the
    boundary walk if needed). Each reflective one must be in our list (it has a pi/4
    corner at e0: the roots of e0^perp = <1,1> are +-e1, +-e2, +-e1+-e2, four mirrors).
Writes data/diagonal_<D>.json.  Usage: diagonal_check.py [NMAX] [WORKERS] [--D=5]
"""
import json
import os
import signal
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import get_ring, from_json, assoc_key, is_squarefree  # noqa: E402
from zphi.chamber import chamber_search  # noqa: E402
from zphi.vinberg import check_polygon  # noqa: E402
from zphi.isometry import find_isometry, invariant_key  # noqa: E402
from zphi.linalg import mat_mul, transpose, det, bil  # noqa: E402

_ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
D = int(next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--D=")), 5))
R = get_ring(D)
NMAX = int(_ARGS[0]) if len(_ARGS) > 0 else 200
WORKERS = int(_ARGS[1]) if len(_ARGS) > 1 else 8
LIMIT = 1800


def diag(d):
    return [[d[i] if i == j else R(0) for j in range(3)] for i in range(3)]


def chamber_of_diag(dd):
    """Certified chamber of <dd,1,1> (dd < 0 < sigma(dd)), or a status string."""
    from zphi.walk import boundary_walk
    G = diag([dd, R(1), R(1)])
    # generic timelike control vector (1, 1/k, 1/(k+4)); k = 7 reproduces the original
    # Z[phi] run, larger k is needed when |dd| is small at id (e.g. over Q(sqrt13))
    k = 7
    while True:
        v0 = [R(1), R(1, 0, k), R(1, 0, k + 4)]
        if bil(G, v0, v0).sign() < 0:
            break
        k = 2 * k + 1
    res = chamber_search(G, v0, max_hops=150)
    if res["status"] == "closed":
        roots = res["roots"]
        if check_polygon(G, roots)["ok"]:
            return G, "reflective", roots
    # walk from the pi/4 corner at e0: walls e2 and e1 - e2 (oriented by the chamber
    # containing e0 + small): roots a = e2, b = e1 - e2 meet at angle pi/4 at e0
    a = [R(0), R(0), R(1)]
    b = [R(0), R(1), R(-1)]
    w = boundary_walk(G, a, b, [R(1), R(0), R(0)])
    if w["status"] == "closed":
        if check_polygon(G, w["roots"])["ok"]:
            return G, "reflective", w["roots"]
        return G, "uncertified", w["roots"]
    if w["status"] == "translation":
        from zphi.nonrefl import check_nonreflective
        c = check_nonreflective(G, w["cert"])
        return G, "nonreflective" if c["ok"] else "uncertified", None
    return G, "undetermined", None


class _T(BaseException):
    pass


def _alarm(*_):
    raise _T()


def run_d(dj):
    d = from_json(R, dj)
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(LIMIT)
    try:
        G, st, roots = chamber_of_diag(-d)
    except _T:
        return {"d": dj, "status": "timeout"}
    except Exception as e:  # recorded, never guessed
        return {"d": dj, "status": "error", "err": repr(e)[:200]}
    finally:
        signal.alarm(0)
    out = {"d": dj, "status": st}
    if roots is not None:
        out["roots"] = [[x.to_json() for x in v] for v in roots]
    return out


def diag_values(nmax):
    seen, out = set(), []
    for b in range(-60, 61):
        for a in range(-100, 101):
            z = R(a, b)
            if z.is_zero() or z.sign() <= 0 or z.conj().sign() >= 0:
                continue
            n = -z.norm_num()
            if n > nmax or not is_squarefree(z):
                continue
            k = assoc_key(z)
            if k in seen:
                continue
            seen.add(k)
            out.append(z)
    return sorted(out, key=lambda z: -z.norm_num())


def main():
    data = json.load(open(os.path.join(ROOT, "data", f"cand_classes_{D}.json")))
    import glob
    reps = {}
    want = {c[0] for c in data["classes"]}
    for f in glob.glob(os.path.join(ROOT, "checkpoints", "cand", str(D), "**", "*.jsonl"),
                       recursive=True):
        for line in open(f):
            r = json.loads(line)
            lab = f"{r['kind']}|{json.dumps(r['key'])}|{r['li']}"
            if r["status"] == "reflective" and lab in want and lab not in reps:
                reps[lab] = ([[from_json(R, x) for x in row] for row in r["gram"]],
                             [[from_json(R, x) for x in v] for v in r["roots"]])
    # (a)
    part_a = []
    b2 = []
    for lab, (G, rts) in reps.items():
        ang = check_polygon(G, rts)["angles"]
        if 4 not in ang:
            continue
        b2.append(lab)
        Gd, st, droots = chamber_of_diag(det(G))
        rec = {"class": lab, "det": det(G).to_json(), "angles": ang, "diag_status": st}
        if st == "reflective":
            P = find_isometry(Gd, droots, G, rts)
            if P is not None:
                assert mat_mul(mat_mul(transpose(P), G), P) == Gd
                rec["phi"] = [[x.to_json() for x in row] for row in P]
        rec["ok"] = "phi" in rec
        part_a.append(rec)
        print(json.dumps({k: v for k, v in rec.items() if k != "phi"}), flush=True)
    # (b)
    from multiprocessing import Pool
    ds = diag_values(NMAX)
    print(f"(b): {len(ds)} values of d with |N(d)| <= {NMAX}", flush=True)
    with Pool(WORKERS) as pool:
        part_b = list(pool.imap_unordered(run_d, [z.to_json() for z in ds], chunksize=1))
    keyed = {lab: invariant_key(*reps[lab]) for lab in b2}
    for rec in part_b:
        if rec["status"] != "reflective":
            continue
        d = from_json(R, rec["d"])
        G = diag([-d, R(1), R(1)])
        roots = [[from_json(R, x) for x in v] for v in rec["roots"]]
        rec["in_list"] = None
        k = invariant_key(G, roots)
        for lab in b2:
            if keyed[lab] == k and find_isometry(G, roots, *reps[lab]) is not None:
                rec["in_list"] = lab
                break
    from collections import Counter
    summ = {"a_classes_with_pi4": len(part_a), "a_ok": sum(r["ok"] for r in part_a),
            "b_values": len(part_b), "b_status": dict(Counter(r["status"] for r in part_b)),
            "b_reflective_missing": [r["d"] for r in part_b
                                     if r["status"] == "reflective" and not r.get("in_list")]}
    print(json.dumps(summ), flush=True)
    json.dump({"summary": summ, "a": part_a, "b": part_b},
              open(os.path.join(ROOT, "data", f"diagonal_{D}.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
