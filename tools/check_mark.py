"""Verify every entry of Mark's appendix with our Vinberg implementation.

    python tools/check_mark.py [workers]

For each entry: (a) check_polygon on the printed roots (non-symmetric entries; for
symmetric ones only one period is printed); (b) Vinberg's algorithm from the vertex
of the printed r1, r2; (c) the printed roots must be among Vinberg's simple roots
(compared as mirrors: up to sign and unit multiples) and, for non-symmetric entries,
the two sets must be equal. Results: checkpoints/mark_check/<idx>.json, summary in
data/mark_check.json.
"""
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import ZS2 as R, from_json, gcd_list  # noqa: E402
from zphi.vinberg import vinberg, vinberg_interior, check_polygon, vertex_vector, _emb_val, _sqrt_bounds  # noqa: E402
from zphi.linalg import bil  # noqa: E402
from zphi.chamber import chamber_search  # noqa: E402
from fractions import Fraction as Fr  # noqa: E402
from math import isqrt  # noqa: E402

CK = os.path.join(ROOT, "checkpoints", "mark_check")


def mirror_key(r):
    """Canonical key of the line K r: scale so the first nonzero coordinate is 1."""
    for x in r:
        if not x.is_zero():
            return tuple((y / x).coords() for y in r)


def interior_point(G, rts, closed):
    """A point strictly inside the chamber: positive rational combination of the
    vertices r_i ∩ r_{i+1} of the printed (consecutive) roots, each scaled by a
    rational ~ 1/sqrt|v^2| so the point is central. Checked: r.v0 < 0 for every
    printed root, and v0 timelike."""
    R = G[0][0].R
    s = _sqrt_bounds(R.disc)[0]
    pts = []
    n = len(rts)
    for i in range(n if closed else n - 1):
        p = vertex_vector(G, rts[i], rts[(i + 1) % n])
        j = next(j for j in range(n) if j not in (i, (i + 1) % n)
                 and not bil(G, rts[j], p).is_zero())
        if bil(G, rts[j], p).sign() > 0:
            p = [-x for x in p]
        q = -_emb_val(bil(G, p, p), s)
        c = Fr(1, max(1, isqrt(int(q) + 1)))
        pts.append([R(c) * x for x in p])
    v0 = [sum((p[k] for p in pts), R.zero) for k in range(3)]
    assert all(bil(G, r, v0).sign() < 0 for r in rts), "v0 not interior"
    assert bil(G, v0, v0).sign() < 0
    return v0


def work(idx):
    path = os.path.join(CK, f"{idx:04d}.json")
    if os.path.exists(path):
        return json.load(open(path))
    E = json.load(open(os.path.join(ROOT, "data", "mark_zsqrt2_432.json")))
    e = E[idx]
    G = [[from_json(R, x) for x in row] for row in e["gram"]]
    rts = [[from_json(R, x) for x in r] for r in e["roots"]]
    out = {"idx": idx, "table": e["table"], "angles": e["angles_text"],
           "sym": e["symmetry_order"]}
    t = time.time()
    if e["symmetry_order"] == 1:
        c = check_polygon(G, rts)
        out["cert_ok"] = c["ok"]
        out["cert_issues"] = c["issues"][:3]
    out["cert_s"] = round(time.time() - t, 2)
    t = time.time()
    try:
        closed = e["symmetry_order"] == 1
        if closed or len(rts) >= 4:        # >= 3 vertices: the sum is interior
            v0 = interior_point(G, rts, closed)
            cs = chamber_search(G, v0)
            out["start"] = "hop"
            out["hops"] = cs["hops"]
            # the search is a heuristic; the certificate below is the proof
            v = {"status": "reflective" if cs["status"] == "closed" else "undetermined",
                 "roots": cs["roots"],
                 "cycle": list(range(len(cs["roots"]))) if cs["status"] == "closed" else None}
        else:
            v = vinberg(G, rts[:2], max_roots=200, orient=rts[2])
            out["start"] = "vertex"
        out["vinberg"] = v["status"]
        out["n_roots"] = len(v["roots"])
        vk = {mirror_key(r) for r in v["roots"]}
        mk = {mirror_key(r) for r in rts}
        out["printed_subset"] = mk <= vk
        out["equal"] = (vk == mk) if e["symmetry_order"] == 1 else \
            (len(vk) == len(mk) * e["symmetry_order"])
        out["roots"] = [[x.to_json() for x in r] for r in v["roots"]]
        out["cycle"] = v["cycle"]
        if v["status"] == "reflective":     # certificate on the full chamber
            full = [v["roots"][k] for k in v["cycle"]]
            c = check_polygon(G, full)
            out["full_cert_ok"] = c["ok"]
            out["full_cert_issues"] = c["issues"][:3]
            if not c["ok"]:
                out["vinberg"] = "certificate_failed"
    except Exception as ex:  # recorded, never hidden
        out["vinberg"] = "error"
        out["error"] = repr(ex)
    out["vinberg_s"] = round(time.time() - t, 2)
    os.makedirs(CK, exist_ok=True)
    tmp = path + ".tmp"
    json.dump(out, open(tmp, "w"))
    os.replace(tmp, path)
    return out


def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else os.cpu_count()
    n = len(json.load(open(os.path.join(ROOT, "data", "mark_zsqrt2_432.json"))))
    from multiprocessing import Pool
    from collections import Counter
    res = []
    t0 = time.time()
    with Pool(workers) as pool:
        for k, r in enumerate(pool.imap_unordered(work, range(n))):
            res.append(r)
            if (k + 1) % 25 == 0:
                print(f"{k+1}/{n} {time.time()-t0:.0f}s", flush=True)
    res.sort(key=lambda r: r["idx"])
    summ = {
        "n": n,
        "vinberg": dict(Counter(r["vinberg"] for r in res)),
        "cert_ok": sum(1 for r in res if r.get("cert_ok")),
        "cert_checked": sum(1 for r in res if "cert_ok" in r),
        "printed_subset": sum(1 for r in res if r.get("printed_subset")),
        "equal": sum(1 for r in res if r.get("equal")),
    }
    print(json.dumps(summ))
    json.dump({"summary": summ, "entries": res},
              open(os.path.join(ROOT, "data", "mark_check.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
