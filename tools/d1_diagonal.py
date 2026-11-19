"""D1, diagonal stage: the series L_k = <-d, 1, ..., 1> (2 + k ones) for the reflective
diagonal rank-3 classes, by AlVin (Guglielmetti) with CoxIter cross-checks.

For each reflective <-d,1,1> (data/diagonal_{D}.json, status "reflective") and k = 0, 1, ...:
  * AlVin is run over Q[sqrt D] on -d, 1, ..., 1 with a time limit;
  * if it ends, CoxIter must report finite covolume and cocompactness for the Coxeter graph
    it wrote (and AlVin must report signature (2+k, 1)): the record is "reflective";
  * the first k at which AlVin does not end within the limit is recorded as "open"
    ("not terminated within T s") and the series stops there. This is NOT a
    non-reflectivity certificate (no rank >= 4 witness tool yet). Stopping at the first
    failure uses Bugaenko's propagation result (ROADMAP D1, OPEN_QUESTIONS Q9), not yet
    confirmed from the source: an "open" k is reported as such, never as non-reflective.
k = 0 is the rank-3 form itself (a consistency check against our own chamber).
k is capped by Vinberg's bound (no reflective arithmetic forms in dimension >= 30).

Records go to data/d1_diag_{D}.jsonl, one per (d, k); the run is restartable (forms with a
final record are skipped). Run the script itself under caffeinate, nice and tools/memcap.sh
(the cap covers the whole process tree: AlVin and CoxIter are its children).

Usage: caffeinate -i nice -n 19 tools/memcap.sh 4000 .venv/bin/python tools/d1_diagonal.py D
         [--timeout=600] [--procs=4] [--anchor] [--graphs]
  --graphs: rerun the reflective records, saving the Coxeter graphs (k >= 1) and checking
  AlVin's rank-3 roots against our chamber (k = 0).
  --anchor: only Bugaenko's <-phi, 1^n> (reflective for n <= 7), as a regression check.
"""
from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import time
from multiprocessing import Pool

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
from alvin_crosscheck import _run_pty, alvin_coeff  # noqa: E402

ALVIN = ROOT / "tools/src/AlVin/build/alvin"
COXITER = ROOT / "tools/src/CoxIter/build/coxiter"
KMAX = 27  # dimension 2 + k <= 29 (Vinberg)

args = [a for a in sys.argv[1:] if not a.startswith("--")]
opts = dict((a[2:].split("=", 1) + [""])[:2] for a in sys.argv[1:] if a.startswith("--"))
D = int(args[0]) if args else 5
TIMEOUT = int(opts.get("timeout", 600))
PROCS = int(opts.get("procs", 4))


def run_alvin(d, k):
    coeffs = [alvin_coeff((-d[0], -d[1]))] + ["1"] * (2 + k)
    cmd = [str(ALVIN), f"-k=Q[sqrt {D}]", "-qf", ",".join(coeffs)]  # killed by PID on timeout
    with tempfile.TemporaryDirectory() as td:
        (pathlib.Path(td) / "output").mkdir()
        t0 = time.time()
        out, timed_out = _run_pty(cmd, td, TIMEOUT)
        secs = time.time() - t0
        graphs = list((pathlib.Path(td) / "output").glob("*.coxiter"))
        graph = graphs[0].read_text() if graphs else None
    root_lines = [m.group(1).split(",") for m in
                  (re.match(r"\s*e\d+\s*=\s*\((.*)\)\s*$", line) for line in out.splitlines()) if m]
    nroots = len(root_lines)
    header = re.search(r"Quadratic form \((\d+),(\d+)\)", out)
    return dict(ended=("Algorithm ended" in out) and not timed_out, timed_out=timed_out,
                nroots=nroots, secs=round(secs, 1), root_lines=root_lines,
                signature=[int(header.group(1)), int(header.group(2))] if header else None,
                says_nonreflective=bool(re.search(r"not reflective", out, re.I)),
                graph=graph)


def run_coxiter(graph):
    p = subprocess.run([str(COXITER), "-c", "-fv"], input=graph, capture_output=True,
                       text=True, timeout=3600)
    grab = lambda pat: (re.search(pat, p.stdout) or [None, None])[1]
    return dict(cocompact=grab(r"Cocompact: (\w+)"),
                finite_covolume=grab(r"Finite covolume: (\w+)"),
                dimension=grab(r"Dimension: (\d+)"))


def series(d):
    """Records for k = 0, 1, ... up to the first k that does not end (or KMAX)."""
    recs = []
    for k in range(KMAX + 1):
        al = run_alvin(d, k)
        rec = dict(D=D, d=list(d), k=k, rank=3 + k, timeout_s=TIMEOUT,
                   **{x: al[x] for x in al if x not in ("graph", "root_lines")})
        if al["ended"] and al["graph"]:
            gdir = ROOT / f"data/d1_graphs_{D}"
            gdir.mkdir(exist_ok=True)
            gname = f"d{d[0]}_{d[1]}_k{k}.coxiter"
            (gdir / gname).write_text(al["graph"])  # for the manuscript's diagrams
            rec["graph_file"] = f"data/d1_graphs_{D}/{gname}"
            cx = run_coxiter(al["graph"])
            rec["coxiter"] = cx
            ok = (cx["finite_covolume"] == "yes" and cx["cocompact"] == "yes"
                  and al["signature"] == [2 + k, 1])
            rec["status"] = "reflective" if ok else "inconsistent"
        else:
            rec["status"] = "open"
        recs.append(rec)
        if rec["status"] != "reflective":
            break
    kmax = max((r["k"] for r in recs if r["status"] == "reflective"), default=None)
    final = dict(D=D, d=list(d), final=True, k_reflective_max=kmax,
                 stop=recs[-1]["status"], stop_k=recs[-1]["k"], timeout_s=TIMEOUT)
    return recs + [final]


def graphs_pass():
    """Rerun AlVin on the reflective records: save the Coxeter graph of every reflective
    L_k with k >= 1 (for the manuscript's diagrams), and at k = 0 compare AlVin's roots
    with our chamber (data/diagonal_{D}.json), up to units. Appends one record per run to
    data/d1_graphs_{D}.jsonl."""
    import alvin_crosscheck as AC
    AC.D = D
    ours = {tuple(r["d"]): [[tuple(x) for x in rt] for rt in r["roots"]]
            for r in json.load(open(ROOT / f"data/diagonal_{D}.json"))["b"]
            if r["status"] == "reflective"}
    recs = [json.loads(l) for l in open(ROOT / f"data/d1_diag_{D}.jsonl")]
    todo = [(tuple(r["d"]), r["k"]) for r in recs
            if not r.get("final") and r["status"] == "reflective"]
    gdir = ROOT / f"data/d1_graphs_{D}"
    gdir.mkdir(exist_ok=True)
    with open(ROOT / f"data/d1_graphs_{D}.jsonl", "w") as f:
        for d, k in todo:
            al = run_alvin(d, k)
            rec = dict(D=D, d=list(d), k=k, ended=al["ended"], nroots=al["nroots"],
                       signature=al["signature"])
            if al["ended"] and al["graph"] and k >= 1:
                gname = f"d{d[0]}_{d[1]}_k{k}.coxiter"
                (gdir / gname).write_text(al["graph"])
                rec["graph_file"] = f"data/d1_graphs_{D}/{gname}"
            if k == 0:
                roots = [[AC.parse_entry(t) for t in line] for line in al.get("root_lines", [])]
                mine = ours.get(d, [])
                rec["roots_match_ours"] = (len(roots) == len(mine) and all(
                    any(AC.same_up_to_unit(list(a), o) for a in roots) for o in mine))
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(json.dumps(rec), flush=True)


def main():
    assert ALVIN.exists() and COXITER.exists(), "run tools/build_alvin.sh first"
    if "graphs" in opts:
        return graphs_pass()
    if "anchor" in opts:
        forms = [(0, 1)]  # -phi (Bugaenko 1984: reflective for n <= 7, i.e. k <= 5)
        outp = ROOT / f"data/d1_diag_{D}_anchor.jsonl"
    else:
        recs = json.load(open(ROOT / f"data/diagonal_{D}.json"))["b"]
        forms = [tuple(r["d"]) for r in recs if r["status"] == "reflective"]
        outp = ROOT / f"data/d1_diag_{D}.jsonl"
    done = set()
    if outp.exists():
        for line in open(outp):
            r = json.loads(line)
            if r.get("final"):
                done.add(tuple(r["d"]))
    todo = [d for d in forms if d not in done]
    print(json.dumps(dict(D=D, forms=len(forms), todo=len(todo), timeout_s=TIMEOUT)), flush=True)
    with open(outp, "a") as f, Pool(PROCS) as pool:
        for recs in pool.imap_unordered(series, todo):
            for r in recs:
                f.write(json.dumps(r) + "\n")
            f.flush()
            print(json.dumps(recs[-1]), flush=True)


if __name__ == "__main__":
    main()
