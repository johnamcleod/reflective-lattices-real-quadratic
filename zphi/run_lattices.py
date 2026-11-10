"""Restartable, parallel lattice stage.

    python -m zphi.run_lattices D KIND [workers] [chunk]

1. Configuration keys are generated once into
   checkpoints/lat/<D>/<KIND>/keys.jsonl (deterministic order).
2. Chunks of keys are processed in parallel; chunk i writes chunk_<i>.jsonl and is
   skipped on rerun if present (written atomically via rename).
3. For each configuration: every reflection-stable enlargement M (roots primitive),
   whether its primitive rescaling is SSF, and for SSF ones Mark's local
   simplicity test (zphi.lattices.local_simplicity).
4. `summary(D, KIND)` aggregates per Mark type.
"""
from __future__ import annotations

import glob
import json
import os
import sys
import time
from collections import Counter

from .configs import ENUMERATORS, build, is_triangle
from .lattices import candidates, local_simplicity
from .linalg import det
from .ring import from_json, get_ring

BASE = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    "checkpoints", "lat")


def _dir(D, kind):
    return os.path.join(BASE, str(D), kind)


def _ab_slices(R, kind):
    from .boxes import box, factorisations, gammas
    if kind == "short_edge":
        zs = [g for m, g in sorted(gammas(R).items()) if m != 2]
    else:
        zs = box(R, 4, 36)
    return [f for z in zs for f in factorisations(z)]


def _keys_for_slice(args):
    D, kind, i = args
    R = get_ring(D)
    A0, B0 = _ab_slices(R, kind)[i]
    return i, [cfg.key_json() for cfg in
               ENUMERATORS[kind](R, AB_filter=lambda A, B: A == A0 and B == B0)]


def ensure_keys(D: int, kind: str, workers: int = None) -> str:
    """Generate all configuration keys (parallel over (A,B) slices; the file lists
    slices in slice order, so the order is deterministic)."""
    d = _dir(D, kind)
    os.makedirs(d, exist_ok=True)
    path = os.path.join(d, "keys.jsonl")
    if not os.path.exists(path):
        R = get_ring(D)
        n = len(_ab_slices(R, kind))
        from multiprocessing import Pool
        res = {}
        with Pool(workers or os.cpu_count()) as pool:
            for i, ks in pool.imap_unordered(_keys_for_slice, [(D, kind, i) for i in range(n)]):
                res[i] = ks
        tmp = path + ".tmp"
        with open(tmp, "w") as f:
            for i in range(n):
                for kj in res[i]:
                    f.write(json.dumps(kj) + "\n")
        os.replace(tmp, path)
    return path


def process_key(D, kind, kj):
    R = get_ring(D)
    key = tuple(from_json(R, x) for x in kj)
    cfg = build(kind, key)
    rec = {"key": kj, "type": cfg.mark_type, "enlargements": 0, "lattices": []}
    tri = is_triangle(cfg)
    for GM, Mb, ssf in candidates(cfg.G, cfg.roots, ssf_prune=False):
        rec["enlargements"] += 1
        if not ssf:
            continue
        ok, info = local_simplicity(cfg.G, Mb, cfg.roots, kind, tri)
        rec["lattices"].append({
            "gram": [[e.to_json() for e in row] for row in GM],
            "basis": [[e.to_json() for e in row] for row in Mb],
            "det": det(GM).to_json(),
            "locally_simple": ok,
            "vertices": info,
        })
    return rec


def run_chunk(args):
    D, kind, i, keys = args
    path = os.path.join(_dir(D, kind), f"chunk_{i:05d}.jsonl")
    if os.path.exists(path):
        return i, 0.0
    t0 = time.time()
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        for kj in keys:
            f.write(json.dumps(process_key(D, kind, kj)) + "\n")
    os.replace(tmp, path)
    return i, time.time() - t0


def run(D: int, kind: str, workers: int = None, chunk: int = 100):
    path = ensure_keys(D, kind, workers)
    with open(path) as f:
        keys = [json.loads(line) for line in f]
    jobs = [(D, kind, i, keys[i * chunk:(i + 1) * chunk])
            for i in range((len(keys) + chunk - 1) // chunk)]
    from multiprocessing import Pool
    t0 = time.time()
    done = 0
    with Pool(workers or os.cpu_count()) as pool:
        for i, sec in pool.imap_unordered(run_chunk, jobs):
            done += 1
            if done % 20 == 0 or done == len(jobs):
                print(f"{kind} D={D}: {done}/{len(jobs)} chunks, "
                      f"{time.time() - t0:.0f}s", flush=True)
    return summary(D, kind)


def records(D: int, kind: str):
    for p in sorted(glob.glob(os.path.join(_dir(D, kind), "chunk_*.jsonl"))):
        with open(p) as f:
            for line in f:
                yield json.loads(line)


def summary(D: int, kind: str) -> dict:
    out = {}
    for rec in records(D, kind):
        t = out.setdefault(rec["type"], Counter())
        t["configs"] += 1
        t["enlargements"] += rec["enlargements"]
        t["ssf"] += len(rec["lattices"])
        t["ssf_locally_simple"] += sum(L["locally_simple"] for L in rec["lattices"])
    return {k: dict(v) for k, v in sorted(out.items())}


if __name__ == "__main__":
    D, kind = int(sys.argv[1]), sys.argv[2]
    w = int(sys.argv[3]) if len(sys.argv) > 3 else None
    c = int(sys.argv[4]) if len(sys.argv) > 4 else 100
    print(json.dumps(run(D, kind, w, c)), flush=True)
