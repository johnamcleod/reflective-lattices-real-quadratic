"""Kernel-check certificate classes emitted in split form (cert_all.py --split).

A class C### consists of C###/Base.lean, C###/P###.lean (imports Base) and C###.lean (the
main module; imports Base and all parts, proves `reflective`). Each module is compiled by
its own `lean` process (under tools/memcap.sh, Lean's -M, -j threads, nice 19, caffeinate on macOS),
writing its .olean at its module path in lake's build directory (lean resolves the
ReflectZphi package to one directory). Lake has no trace for these files and would rebuild
them on a later `lake build` of the certificate modules; no other lake target imports them. The parts of one class run up to
`--jobs` at a time. The main module gets `#print axioms reflective` appended (in a
temporary copy). One JSON record per class goes to logs/check_split_{D}.jsonl, with the
per-module peak RSS and user time; classes recorded ok are skipped (restartable).

Monolithic classes (no C### directory) are checked the same way, as a single module.

--recheck: check every class again against the files now on disk, logging to
logs/recheck_{D}.jsonl (restartable on that log). Parts whose stamp matches their current source
(and Base) are reused; main modules and monolithic classes are recompiled, with their axioms.
Each record gets "reused" = the number of parts taken from matching stamps.

--olean: like --recheck (log logs/olean_{D}.jsonl), but every main module and monolithic class is
compiled from its own source to its .olean (with a stamp; no #print axioms), and at the end
Data/Cert{D}.lean and ReflectZphi/Results.lean are compiled, so that Results.lean is checked
against the certificates: its `#print axioms all_reflective` and `#audit_axioms` output goes
to logs/results_{D}.out. Results.lean then compiles without errors only if all is well.

Usage: python tools/check_split.py D [--jobs=2] [--mem=4000] [--threads=1] [--only=a,b,...] [--recheck | --olean]
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOT = os.path.abspath(".")
LEAN_DIR = os.path.join(ROOT, "lean")
BUILD = os.path.join(LEAN_DIR, ".lake", "build", "lib", "lean")


def wrap():
    """Command prefix: timing (BSD `time -l` on macOS, GNU `time -v` on Linux), caffeinate on
    macOS only, nice 19."""
    if sys.platform == "darwin":
        return ["/usr/bin/time", "-l", "caffeinate", "-i", "nice", "-n", "19"]
    if os.path.exists("/usr/bin/time"):
        return ["/usr/bin/time", "-v", "nice", "-n", "19"]
    return ["nice", "-n", "19"]


def parse_time(out):
    """(user seconds, max RSS in MB) from the output of BSD or GNU /usr/bin/time."""
    user = re.search(r"([\d.]+) user", out) or re.search(r"User time \(seconds\): ([\d.]+)", out)
    rss = re.search(r"(\d+)\s+maximum resident set size", out)            # bytes (BSD)
    rss_mb = int(rss.group(1)) // 2**20 if rss else None
    if rss is None:
        k = re.search(r"Maximum resident set size \(kbytes\): (\d+)", out)  # GNU
        rss_mb = int(k.group(1)) // 1024 if k else None
    return (float(user.group(1)) if user else None), rss_mb


def lean_env():
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_DIR,
                         capture_output=True, text=True, check=True).stdout.strip()
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=LEAN_DIR,
                          capture_output=True, text=True, check=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=out, MEMCAP_REPORT="1")
    return lean, env


def stamp(src, deps):
    h = hashlib.sha256()
    for f in [src, *deps]:
        h.update(open(f, "rb").read())
    return h.hexdigest()


def run_module(lean, env, src, olean, mem, threads, append_axioms=False, tmpdir=None, deps=()):
    """Compile one module; returns a record (rc, user, rss_mb, errors, axioms).
    A module with an .olean whose recorded stamp (hash of its source and of `deps`) matches
    was compiled successfully before from the same text, and is reused."""
    if olean and os.path.exists(olean) and os.path.exists(olean + ".stamp") and \
            open(olean + ".stamp").read() == stamp(src, deps):
        return dict(mod=os.path.relpath(src, LEAN_DIR), rc=0, user=0.0, rss_mb=None, fp_mb=None,
                    errors=[], reused=True)
    if olean and os.path.exists(olean + ".stamp"):
        os.remove(olean + ".stamp")
    path = src
    if append_axioms:
        text = open(src).read()
        ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
        path = os.path.join(tmpdir, os.path.basename(src))
        open(path, "w").write(text.replace(f"end {ns}\n", f"#print axioms reflective\nend {ns}\n"))
    cmd = wrap() + [os.path.join(ROOT, "tools/memcap.sh"), str(mem),
           lean, f"-M{mem + 3000}", f"-j{threads}"]  # -M counts mapped oleans (~3 GB); memcap is the real cap
    if olean:
        os.makedirs(os.path.dirname(olean), exist_ok=True)
        cmd += ["-o", olean]
    cmd += [path]
    p = subprocess.run(cmd, cwd=LEAN_DIR, env=env, capture_output=True, text=True)
    out = p.stdout + p.stderr
    user, rss_mb = parse_time(out)
    fp = re.search(r"memcap: peak footprint (\d+) MB", out)
    errors = [l for l in out.splitlines() if ": error" in l or l.startswith("memcap: footprint")]
    ax = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    rec = dict(mod=os.path.relpath(src, LEAN_DIR), rc=p.returncode,
               user=user, rss_mb=rss_mb,
               fp_mb=int(fp.group(1)) if fp else None, errors=errors[:5])
    if append_axioms:
        rec["axioms"] = [a.strip() for a in ax.group(1).split(",")] if ax else None
    if p.returncode != 0 and not errors:
        rec["tail"] = [l for l in out.strip().splitlines() if "abort" in l or "exception" in l
                       or "error" in l.lower()][-4:] or out.strip().splitlines()[:4]
    if olean and p.returncode == 0 and not errors:
        open(olean + ".stamp", "w").write(stamp(src, deps))
    return rec


def check_class(D, ci, lean, env, mem, threads, jobs, tmpdir, olean=False):
    rel = f"ReflectZphi/Data/Cert{D}/C{ci:03d}"
    src_main = os.path.join(LEAN_DIR, rel + ".lean")
    sub = os.path.join(LEAN_DIR, rel)
    t0 = time.time()
    mods = []
    ok = True
    if os.path.isdir(sub):
        base = run_module(lean, env, os.path.join(sub, "Base.lean"),
                          os.path.join(BUILD, rel, "Base.olean"), mem, threads)
        mods.append(base)
        ok = base["rc"] == 0 and not base["errors"]
        parts = sorted(f[:-5] for f in os.listdir(sub) if f.startswith("P") and f.endswith(".lean"))
        if ok:
            with ThreadPoolExecutor(jobs) as ex:
                recs = list(ex.map(lambda m: run_module(
                    lean, env, os.path.join(sub, m + ".lean"),
                    os.path.join(BUILD, rel, m + ".olean"), mem, threads,
                    deps=[os.path.join(sub, "Base.lean")]), parts))
            mods += recs
            ok = all(r["rc"] == 0 and not r["errors"] for r in recs)
    main = None
    if ok and olean:
        deps = [os.path.join(sub, f) for f in sorted(os.listdir(sub)) if f.endswith(".lean")] \
            if os.path.isdir(sub) else []
        main = run_module(lean, env, src_main, os.path.join(BUILD, rel + ".olean"), mem, threads,
                          deps=deps)
        mods.append(main)
        ok = main["rc"] == 0 and not main["errors"]
    elif ok:
        main = run_module(lean, env, src_main, None, mem, threads, append_axioms=True, tmpdir=tmpdir)
        mods.append(main)
        ok = (main["rc"] == 0 and not main["errors"] and main["axioms"] is not None
              and set(main["axioms"]) <= ALLOWED)
    users = [m["user"] for m in mods if m["user"] is not None]
    rss = [m["rss_mb"] for m in mods if m["rss_mb"] is not None]
    fps = [m["fp_mb"] for m in mods if m.get("fp_mb") is not None]
    return dict(cls=ci, ok=ok, modules=len(mods), user=round(sum(users), 1),
                wall=round(time.time() - t0, 1), max_rss_mb=max(rss) if rss else None, max_fp_mb=max(fps) if fps else None,
                axioms=main.get("axioms") if main else None,
                failed=[m for m in mods if m["rc"] != 0 or m["errors"]][:3],
                reused=sum(1 for m in mods if m.get("reused")),
                per_module=[(m["mod"].split("/")[-1], m["user"], m["rss_mb"], m.get("fp_mb")) for m in mods])


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = dict((a[2:].split("=", 1) + [""])[:2] for a in sys.argv[1:] if a.startswith("--"))
    D = int(args[0])
    jobs, mem, threads = int(opts.get("jobs", 2)), int(opts.get("mem", 4000)), int(opts.get("threads", 1))
    olean = "olean" in opts
    mode = "olean" if olean else ("recheck" if "recheck" in opts else "check_split")
    logp = os.path.join(ROOT, f"logs/{mode}_{D}.jsonl")
    done = set()
    if os.path.exists(logp):
        for l in open(logp):
            r = json.loads(l)
            if r["ok"]:
                done.add(r["cls"])
    if "only" in opts:
        classes = [int(x) for x in opts["only"].split(",")]
    else:
        d = os.path.join(LEAN_DIR, f"ReflectZphi/Data/Cert{D}")
        classes = sorted(int(f[1:4]) for f in os.listdir(d) if f.endswith(".lean"))
    classes = [c for c in classes if c not in done]
    d = os.path.join(LEAN_DIR, f"ReflectZphi/Data/Cert{D}")
    missing = [c for c in classes if not os.path.exists(os.path.join(d, f"C{c:03d}.lean"))]
    if missing:
        print(json.dumps(dict(skipped_not_emitted=missing)), flush=True)
    classes = [c for c in classes if c not in missing]
    lean, env = lean_env()
    log = open(logp, "a")
    with tempfile.TemporaryDirectory() as tmpdir:
        for ci in classes:
            rec = check_class(D, ci, lean, env, mem, threads, jobs, tmpdir, olean=olean)
            print(json.dumps({k: rec[k] for k in rec if k != "per_module"}), flush=True)
            log.write(json.dumps(rec) + "\n"); log.flush()
    if olean and "only" not in opts:
        allok = set()
        for l in open(logp):
            r = json.loads(l)
            if r["ok"]:
                allok.add(r["cls"])
        d = os.path.join(LEAN_DIR, f"ReflectZphi/Data/Cert{D}")
        everything = {int(f[1:4]) for f in os.listdir(d) if f.endswith(".lean")}
        if allok != everything:
            print(json.dumps(dict(results="not compiled", missing=sorted(everything - allok))), flush=True)
            return
        agg = run_module(lean, env, os.path.join(LEAN_DIR, f"ReflectZphi/Data/Cert{D}.lean"),
                         os.path.join(BUILD, f"ReflectZphi/Data/Cert{D}.olean"), mem, threads,
                         deps=[os.path.join(d, f) for f in sorted(os.listdir(d)) if f.endswith(".lean")])
        print(json.dumps(dict(aggregate=agg)), flush=True)
        if agg["rc"] != 0 or agg["errors"]:
            return
        cmd = wrap() + [os.path.join(ROOT, "tools/memcap.sh"), str(mem), lean, f"-M{mem + 3000}",
               f"-j{threads}", os.path.join(LEAN_DIR, "ReflectZphi/Results.lean")]
        p = subprocess.run(cmd, cwd=LEAN_DIR, env=env, capture_output=True, text=True)
        out = p.stdout + p.stderr
        open(os.path.join(ROOT, f"logs/results_{D}.out"), "w").write(out)
        print(json.dumps(dict(results_rc=p.returncode,
                              report=[l for l in out.splitlines() if "axiom" in l or "error" in l])),
              flush=True)


if __name__ == "__main__":
    main()
