"""Kernel-check the emitted certificate modules, a bounded number at a time.

Each module lean/ReflectZphi/Data/Cert{D}/C###.lean is checked by `lake env lean` under
tools/memcap.sh (memory cap on the process tree) and Lean's own -M, with -j threads, at
nice 19 under caffeinate. The axioms of `reflective` are printed by an appended command
(in a temporary copy; the module itself is not changed). One JSON record per class goes to
logs/check_{D}.jsonl; classes already recorded as ok are skipped (restartable).

Usage: python tools/check_certs.py D [--jobs=2] [--mem=4000] [--threads=2] [--only=a,b,...]
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check(D, mod, mem, threads, tmpdir):
    src = f"lean/ReflectZphi/Data/Cert{D}/{mod}.lean"
    text = open(src).read()
    ns = re.search(r"^namespace (\S+)", text, re.M).group(1)
    tmp = os.path.join(tmpdir, f"{mod}.lean")
    open(tmp, "w").write(text.replace(f"end {ns}\n", f"#print axioms reflective\nend {ns}\n"))
    cmd = ["/usr/bin/time", "-p", "caffeinate", "-i", "nice", "-n", "19",
           os.path.abspath("tools/memcap.sh"), str(mem),
           "lake", "env", "lean", f"-M{mem + 3000}", f"-j{threads}", tmp]
    t0 = time.time()
    p = subprocess.run(cmd, cwd="lean", capture_output=True, text=True)
    out = p.stdout + p.stderr
    user = re.search(r"^user\s+([\d.]+)", out, re.M)
    ax = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    axioms = [a.strip() for a in ax.group(1).split(",")] if ax else None
    errors = [l for l in out.splitlines() if ": error" in l or l.startswith("memcap:")]
    ok = p.returncode == 0 and not errors and axioms is not None and set(axioms) <= ALLOWED
    return dict(cls=int(mod[1:]), ok=ok, rc=p.returncode, user=float(user.group(1)) if user else None,
                wall=round(time.time() - t0, 1), axioms=axioms, errors=errors[:5])


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opts = dict(a[2:].split("=", 1) for a in sys.argv[1:] if a.startswith("--"))
    D = int(args[0])
    jobs, mem, threads = int(opts.get("jobs", 2)), int(opts.get("mem", 4000)), int(opts.get("threads", 2))
    logp = f"logs/check_{D}.jsonl"
    done = set()
    if os.path.exists(logp):
        for l in open(logp):
            r = json.loads(l)
            if r["ok"]:
                done.add(r["cls"])
    mods = sorted(f[:-5] for f in os.listdir(f"lean/ReflectZphi/Data/Cert{D}") if f.endswith(".lean"))
    if "only" in opts:
        keep = {int(x) for x in opts["only"].split(",")}
        mods = [m for m in mods if int(m[1:]) in keep]
    # smallest first (by the emitter's node count)
    size = {}
    for l in open(f"logs/cert_{D}.jsonl"):
        r = json.loads(l)
        if "nodes" in r:
            size[r["cls"]] = r["nodes"]
    mods = [m for m in mods if int(m[1:]) not in done]
    mods.sort(key=lambda m: size.get(int(m[1:]), 0))
    log = open(logp, "a")
    with tempfile.TemporaryDirectory() as tmpdir, ThreadPoolExecutor(jobs) as ex:
        for rec in ex.map(lambda m: check(D, m, mem, threads, tmpdir), mods):
            rec["nodes"] = size.get(rec["cls"])
            print(json.dumps(rec), flush=True)
            log.write(json.dumps(rec) + "\n"); log.flush()


if __name__ == "__main__":
    main()
