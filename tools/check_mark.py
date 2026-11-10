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
from zphi.vinberg import vinberg, check_polygon  # noqa: E402

CK = os.path.join(ROOT, "checkpoints", "mark_check")


def mirror_key(r):
    """Canonical key of the line K r: scale so the first nonzero coordinate is 1."""
    for x in r:
        if not x.is_zero():
            return tuple((y / x).coords() for y in r)


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
        v = vinberg(G, rts[:2], max_roots=80, orient=rts[2])
        out["vinberg"] = v["status"]
        out["n_roots"] = len(v["roots"])
        vk = {mirror_key(r) for r in v["roots"]}
        mk = {mirror_key(r) for r in rts}
        out["printed_subset"] = mk <= vk
        out["equal"] = (vk == mk) if e["symmetry_order"] == 1 else \
            (len(vk) == len(mk) * e["symmetry_order"])
        out["roots"] = [[x.to_json() for x in r] for r in v["roots"]]
        out["cycle"] = v["cycle"]
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
