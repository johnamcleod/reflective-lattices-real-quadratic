"""Vinberg's algorithm on every SSF candidate lattice from the lattice stage.

    python tools/run_candidates.py D [workers] [max_roots]

For each SSF enlargement M of a configuration (checkpoints/lat/<D>/<kind>/), the
configuration roots are written in M-coordinates and Vinberg is started at a
configuration vertex whose two roots are simple there (mirror count = m; for locally
simple M every vertex qualifies). The sheet of v0 is fixed by another configuration
root not through v0 (the configuration cell lies on its negative side).

Non-locally-simple M are run too (cross-check; they need not be reflective), when
some vertex qualifies. Results: checkpoints/cand/<D>/<n>.jsonl, one line per
lattice: {kind, key, li, ls, gram, status, roots, cycle, ...}.
"""
import json
import os
from fractions import Fraction as Fr
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.configs import build, is_triangle  # noqa: E402
from zphi.lattices import primitive_gram, vertex_pairs, dihedral_order  # noqa: E402
from zphi.linalg import inv, mat_vec, bil, gram_of  # noqa: E402
from zphi.ring import from_json, get_ring  # noqa: E402
from zphi.run_lattices import records  # noqa: E402
from zphi.vinberg import check_polygon  # noqa: E402
from zphi.chamber import chamber_search  # noqa: E402
from zphi.nonrefl import check_nonreflective  # noqa: E402

KINDS = ("short_edge", "short_pair", "close_pair")
ALL = "--all" in sys.argv   # also run non-locally-simple candidates (cross-check)
def _opt(name, default, conv=int):
    return conv(next((a.split("=", 1)[1] for a in sys.argv if a.startswith(f"--{name}=")), default))


MAX_HOPS = _opt("hops", 40)   # hop budget before "undetermined" (non-reflective never close)
JOB_SECONDS = _opt("limit", 900)
DELTA_HOP = _opt("delta", 64)  # sinh^2 of the hop radius
REDO = _opt("redo", "", str)       # pass name: rerun only unresolved (timeout/undetermined) jobs
SAMPLE = _opt("sample", 0)     # with --redo: only the first N unresolved jobs (experiments)
# wall-clock limit per candidate; exceeded -> status "timeout" (decides nothing)


class _Timeout(BaseException):   # not swallowed by "except Exception"
    pass


def _alarm(signum, frame):
    raise _Timeout()


def jobs(D):
    out = []
    for kind in KINDS:
        for rec in records(D, kind):
            for li, L in enumerate(rec["lattices"]):
                # only locally simple candidates need deciding: every reflective SSF
                # lattice arises from a configuration of its own simple roots, which
                # is locally simple (methods.md)
                if L["locally_simple"] or ALL:
                    out.append((D, kind, rec["key"], li, L))
    return out


def work(args):
    D, kind, kj, li, L, max_roots = args
    R = get_ring(D)
    key = tuple(from_json(R, x) for x in kj)
    cfg = build(kind, key)
    Mb = [[from_json(R, x) for x in row] for row in L["basis"]]
    GM, _ = primitive_gram(gram_of(cfg.G, Mb))
    Minv = inv(Mb)
    rts = [mat_vec(Minv, r) for r in cfg.roots]
    pairs = list(vertex_pairs(kind, len(cfg.roots)))
    if is_triangle(cfg):
        pairs.append((0, 2))
    out = {"kind": kind, "key": kj, "li": li, "ls": L["locally_simple"],
           "gram": [[e.to_json() for e in row] for row in GM]}
    good = [p for p, (m, c) in zip(pairs, L["vertices"]) if m == c]
    if not good:
        out["status"] = "no_simple_vertex"
        return out
    i, j = good[0]
    orient = next((rts[k] for k in range(len(rts)) if k not in (i, j)
                   and not bil(GM, rts[k], _vertex(GM, rts[i], rts[j])).is_zero()), None)
    t = time.time()
    import signal
    print(f"start {kind} {json.dumps(kj)} {li}", file=sys.stderr, flush=True)
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(JOB_SECONDS)
    try:
        cs = chamber_search(GM, start=(rts[i], rts[j]), orient=orient,
                            max_hops=MAX_HOPS, try_translation=True,
                            Delta_hop=Fr(DELTA_HOP))
        out["hops"] = cs["hops"]
        out["roots"] = [[x.to_json() for x in r] for r in cs["roots"]]
        if cs["status"] == "closed":
            c = check_polygon(GM, cs["roots"])     # the proof of reflectivity
            out["status"] = "reflective" if c["ok"] else "certificate_failed"
            out["cert_issues"] = c["issues"][:3]
        elif cs["status"] == "translation":
            c = check_nonreflective(GM, cs["cert"])   # the proof of non-reflectivity
            out["status"] = "nonreflective" if c["ok"] else "nonrefl_cert_failed"
            out["cert"] = cs["cert"]
            out["cert_issues"] = c["issues"][:3]
        else:
            out["status"] = "undetermined"
    except _Timeout:
        out["status"] = "timeout"
        out["limit"] = JOB_SECONDS
    except Exception as ex:   # recorded, never hidden
        out["status"] = "error"
        out["error"] = repr(ex)
    finally:
        signal.alarm(0)
    out["sec"] = round(time.time() - t, 2)
    return out


def _vertex(G, r, s):
    from zphi.vinberg import vertex_vector
    return vertex_vector(G, r, s)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    D = int(args[0])
    workers = int(args[1]) if len(args) > 1 else os.cpu_count()
    max_roots = int(args[2]) if len(args) > 2 else 80
    ck = os.path.join(ROOT, "checkpoints", "cand", str(D))
    os.makedirs(ck, exist_ok=True)
    J = jobs(D)
    print(f"{len(J)} lattices", flush=True)
    def read(dirn):
        out = {}
        for f in sorted(os.listdir(dirn)):
            if f.endswith(".jsonl"):
                for line in open(os.path.join(dirn, f)):
                    r = json.loads(line)
                    out[(r["kind"], json.dumps(r["key"]), r["li"])] = r["status"]
        return out
    first = read(ck)
    if REDO:
        unresolved = {k for k, st in first.items() if st in ("timeout", "undetermined")}
        ck = os.path.join(ck, REDO)
        os.makedirs(ck, exist_ok=True)
        done = set(read(ck))
        J = [j for j in J if (j[1], json.dumps(j[2]), j[3]) in unresolved]
        if SAMPLE:
            J = J[::max(1, len(J) // SAMPLE)][:SAMPLE]
        print(f"pass {REDO}: {len(J)} unresolved; hops={MAX_HOPS} delta={DELTA_HOP} "
              f"limit={JOB_SECONDS}s", flush=True)
    else:
        done = set(first)
    todo = [j + (max_roots,) for j in J if (j[1], json.dumps(j[2]), j[3]) not in done]
    print(f"{len(todo)} to do", flush=True)
    from multiprocessing import Pool
    from collections import Counter
    t0 = time.time()
    path = os.path.join(ck, f"run_{int(t0)}.jsonl")
    with Pool(workers) as pool, open(path, "a") as f:
        for k, r in enumerate(pool.imap_unordered(work, todo, chunksize=1)):
            f.write(json.dumps(r) + "\n")
            f.flush()
            if (k + 1) % 25 == 0:
                print(f"{k+1}/{len(todo)} {time.time()-t0:.0f}s", flush=True)
    allr = [json.loads(line) for fn in sorted(os.listdir(ck)) if fn.endswith(".jsonl")
            for line in open(os.path.join(ck, fn))]
    print(json.dumps({"ls": dict(Counter(r["status"] for r in allr if r["ls"])),
                      "not_ls": dict(Counter(r["status"] for r in allr if not r["ls"]))}))


if __name__ == "__main__":
    main()
