"""Parallel count of close-pair configurations (Lemma 11), split by (A, B).

    python -m zphi.count_close D [workers]

For each (A,B) slice it records the number of keys passing the integrality
conditions (Mark (25)), the number also passing the ultraparallel filter, and the
number of Mark-(26) gamma mismatches against the exact s.s' (should be 0). Results
are checkpointed per slice in checkpoints/close_count/<D>/<i>.json.
"""
from __future__ import annotations

import json
import os
import sys
import time

from .boxes import box, factorisations
from .configs import close_pair, mark_beta, mark_gamma, scaled_gram, mark_matrix
from .ring import get_ring

CK = os.path.join(os.path.dirname(__file__), "..", "checkpoints", "close_count")


def slices(R):
    return [f for z in box(R, 4, 36) for f in factorisations(z)]


def run_slice(args):
    D, i = args
    R = get_ring(D)
    path = os.path.join(CK, str(D), f"{i}.json")
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    A0, B0 = slices(R)[i]
    t0 = time.time()
    st = {}
    n_up = 0
    gamma_bad = 0
    mark_bad = 0
    for cfg in close_pair(R, ultraparallel=False,
                          AB_filter=lambda A, B: A == A0 and B == B0, stats=st):
        G = scaled_gram(cfg)
        ss = G[1][3]
        s2, sp2 = G[1][1], G[3][3]
        up = ss.sign() < 0 and (ss * ss - s2 * sp2).sign() > 0
        n_up += up
        if G != mark_matrix("close_pair", cfg.key):
            mark_bad += 1
    out = {"i": i, "A": A0.to_json(), "B": B0.to_json(),
           "integral": st.get("integral", 0), "ultraparallel": n_up,
           "mark_mismatch": mark_bad, "seconds": round(time.time() - t0, 2)}
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(out, f)
    return out


def main():
    D = int(sys.argv[1])
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else os.cpu_count()
    R = get_ring(D)
    n = len(slices(R))
    from multiprocessing import Pool
    tot = {"integral": 0, "ultraparallel": 0, "mark_mismatch": 0}
    with Pool(workers) as pool:
        for r in pool.imap_unordered(run_slice, [(D, i) for i in range(n)]):
            for k in tot:
                tot[k] += r[k]
            print(json.dumps(r), flush=True)
    print("TOTAL", R.name, json.dumps(tot), flush=True)


if __name__ == "__main__":
    main()
