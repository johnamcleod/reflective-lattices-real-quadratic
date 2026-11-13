"""Independent cross-check of the diagonal family <-d,1,1> over Z[phi] against AlVin and CoxIter.

For each of the 149 SSF admissible <-d,1,1> with |N(d)| <= 400 (data/diagonal_5.json), AlVin
(Guglielmetti) is run over Q[sqrt 5] (its ring of integers Z[phi]; AlVin's T(5) is phi).

  * Our status reflective: AlVin must end, its roots must equal our chamber's roots up to
    units (same set of mirrors, the same chamber), and CoxIter must report the graph as
    cocompact with finite covolume.
  * Our status non-reflective (we hold a certificate): AlVin must not end within the time
    limit, or must report non-reflectivity itself. AlVin ending would be a contradiction.

AlVin and CoxIter are built at pinned commits by tools/build_alvin.sh. Exact arithmetic
throughout; elements of Z[phi] are pairs [a, b] = a + b*phi.

Usage: python3 tools/alvin_crosscheck.py [TIMEOUT_SECONDS] [--rerun-failures] [--D=5|13]
  -> data/alvin_crosscheck_5.json. With --rerun-failures, only the cases that failed in
  the existing file are rerun (with the new time limit) and their results replaced.
"""
import json, pathlib, re, subprocess, sys, tempfile
from fractions import Fraction
from multiprocessing import Pool

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALVIN = ROOT / "tools/src/AlVin/build/alvin"
COXITER = ROOT / "tools/src/CoxIter/build/coxiter"
TIMEOUT = 60
D = int(next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--D=")), 5))
# AlVin's T(d) is the generator w of O = Z[w] in our profiles (phi for d = 5,
# (1 + sqrt13)/2 for d = 13), so coordinates (a, b) = a + b w carry over unchanged.
_C0C1 = {5: (1, 1), 13: (3, 1)}

# --- Z[phi] / Q(sqrt5) arithmetic on pairs (phi^2 = 1 + phi) -----------------------------
def mul(x, y):
    c0, c1 = _C0C1[D]
    a, b = x; c, d = y
    return (a * c + c0 * b * d, a * d + b * c + c1 * b * d)

def conj(x):  # sigma(a + b w) = a + b(c1 - w)
    a, b = x
    return (a + _C0C1[D][1] * b, -b)

def norm(x):
    c0, c1 = _C0C1[D]
    a, b = x
    return a * a + c1 * a * b - c0 * b * b

def div(x, y):  # exact quotient in Q(sqrt5), as a pair of Fractions
    n = norm(y)
    p = mul(x, conj(y))
    return (Fraction(p[0], n), Fraction(p[1], n))

def is_unit(q):
    a, b = q
    return a.denominator == 1 and b.denominator == 1 and abs(norm((int(a), int(b)))) == 1

def same_up_to_unit(r, s):
    """r = u s for a unit u (r, s nonzero vectors over Z[phi])."""
    i = next(k for k, x in enumerate(s) if x != (0, 0))
    if r[i] == (0, 0):
        return False
    u = div(r[i], s[i])
    if not is_unit(u):
        return False
    ui = (int(u[0]), int(u[1]))
    return all(mul(ui, tuple(sx)) == tuple(rx) for rx, sx in zip(r, s))

# --- AlVin I/O -----------------------------------------------------------------------------
def alvin_coeff(x):
    a, b = x
    if b == 0:
        return str(a)
    t = ("" if b == 1 else "-" if b == -1 else str(b)) + "T"
    return t if a == 0 else f"{a}{'+' if b > 0 else ''}{t}"

def parse_entry(s):
    """'-1 + 1 * T(5)', '1 * T(5)', '-T(5)', '3' -> (a, b)."""
    s = s.replace(" ", "")
    a = b = 0
    for tok in re.findall(r"[+-]?[^+-]+", s):
        if f"T({D})" in tok:
            c = tok.replace(f"*T({D})", "").replace(f"T({D})", "")
            b += 1 if c in ("", "+") else -1 if c == "-" else int(c)
        else:
            a += int(tok)
    return (a, b)

def _run_pty(args, cwd, timeout):
    """Run under a pseudo-terminal so that AlVin's stdout is line-buffered: the roots
    printed before a timeout are then not lost. On timeout the child (this PID only)
    is killed."""
    import os, pty, select, time
    master, slave = pty.openpty()
    p = subprocess.Popen(args, cwd=cwd, stdout=slave, stderr=slave, stdin=subprocess.DEVNULL)
    os.close(slave)
    chunks, deadline, timed_out = [], time.monotonic() + timeout, False
    while True:
        left = deadline - time.monotonic()
        if left <= 0:
            timed_out = True
            p.kill()
            break
        r, _, _ = select.select([master], [], [], min(left, 1.0))
        if r:
            try:
                data = os.read(master, 65536)
            except OSError:
                data = b""
            if not data:
                break
            chunks.append(data)
        elif p.poll() is not None:
            break
    p.wait()
    while True:  # drain
        r, _, _ = select.select([master], [], [], 0)
        if not r:
            break
        try:
            data = os.read(master, 65536)
        except OSError:
            break
        if not data:
            break
        chunks.append(data)
    os.close(master)
    return b"".join(chunks).decode(errors="replace"), timed_out


def run_alvin(d, timeout):
    neg = (-d[0], -d[1])
    args = [str(ALVIN), f"-k=Q[sqrt {D}]", "-qf", ",".join([alvin_coeff(neg), "1", "1"])]
    with tempfile.TemporaryDirectory() as td:
        (pathlib.Path(td) / "output").mkdir()
        out, timed_out = _run_pty(args, td, timeout)
        graphs = list((pathlib.Path(td) / "output").glob("*.coxiter"))
        graph = graphs[0].read_text() if graphs else None
    roots = []
    for line in out.splitlines():
        m = re.match(r"\s*e\d+\s*=\s*\((.*)\)\s*$", line)
        if m:
            roots.append([parse_entry(t) for t in m.group(1).split(",")])
    header = re.search(r"Quadratic form \((\d+),(\d+)\):\s*(.*)", out)
    return {"roots": roots, "ended": ("Algorithm ended" in out) and not timed_out,
            "timed_out": timed_out, "graph": graph,
            "says_nonreflective": bool(re.search(r"not reflective", out, re.I)),
            "form": header.group(3).strip() if header else None,
            "signature": [int(header.group(1)), int(header.group(2))] if header else None}

def run_coxiter(graph):
    p = subprocess.run([str(COXITER), "-c", "-fv"], input=graph, capture_output=True,
                       text=True, timeout=300)
    grab = lambda pat: (re.search(pat, p.stdout) or [None, None])[1]
    return {"cocompact": grab(r"Cocompact: (\w+)"),
            "finite_covolume": grab(r"Finite covolume: (\w+)")}

# --- per case ------------------------------------------------------------------------------
def check(rec):
    d = tuple(rec["d"])
    al = run_alvin(d, TIMEOUT)
    res = {"d": list(d), "ours": rec["status"], "alvin_ended": al["ended"],
           "alvin_timed_out": al["timed_out"], "alvin_says_nonreflective": al["says_nonreflective"],
           "alvin_signature": al["signature"], "alvin_form": al["form"],
           "alvin_nroots": len(al["roots"])}
    if rec["status"] == "reflective":
        ours = [[tuple(x) for x in r] for r in rec["roots"]]
        match = (len(ours) == len(al["roots"]) and
                 all(any(same_up_to_unit(a, o) for a in al["roots"]) for o in ours))
        res["roots_match"] = match
        res["alvin_roots_in_ours"] = all(any(same_up_to_unit(a, o) for o in ours)
                                         for a in al["roots"])
        res["ours_nroots"] = len(ours)
        cx = run_coxiter(al["graph"]) if al["graph"] else {}
        res["coxiter"] = cx
        res["ok"] = (al["ended"] and match and al["signature"] == [2, 1]
                     and cx.get("cocompact") == "yes" and cx.get("finite_covolume") == "yes")
    else:
        res["ok"] = not al["ended"]
    return res

def main():
    global TIMEOUT
    nums = [a for a in sys.argv[1:] if a.isdigit()]
    _ = D
    if nums:
        TIMEOUT = int(nums[0])
    assert ALVIN.exists() and COXITER.exists(), "run tools/build_alvin.sh first"
    recs = json.load(open(ROOT / f"data/diagonal_{D}.json"))["b"]
    outp = ROOT / f"data/alvin_crosscheck_{D}.json"
    if "--rerun-failures" in sys.argv:
        prev = json.load(open(outp))["cases"]
        bad = {tuple(r["d"]) for r in prev if not r["ok"]}
        with Pool(8) as pool:
            redo = pool.map(check, [r for r in recs if tuple(r["d"]) in bad], chunksize=1)
        new = {tuple(r["d"]): dict(r, timeout_s=TIMEOUT) for r in redo}
        out = [new.get(tuple(r["d"]), r) for r in prev]
    else:
        with Pool(8) as pool:
            out = pool.map(check, recs, chunksize=1)
    summ = {"timeout_s": TIMEOUT, "cases": len(out), "ok": sum(r["ok"] for r in out),
            "reflective_agree": sum(r["ok"] for r in out if r["ours"] == "reflective"),
            "nonreflective_agree": sum(r["ok"] for r in out if r["ours"] != "reflective"),
            "alvin_says_nonreflective": sum(r["alvin_says_nonreflective"] for r in out),
            "failures": [r for r in out if not r["ok"]]}
    json.dump({"summary": summ, "cases": out}, open(outp, "w"),
              indent=1)
    print(json.dumps({k: v for k, v in summ.items() if k != "failures"}),
          "failures:", [f["d"] for f in summ["failures"]])

if __name__ == "__main__":
    main()
