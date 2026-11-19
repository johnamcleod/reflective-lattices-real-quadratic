"""Root tables of the reflective L_k = <-d, 1^n> (n = 2 + k, hyperbolic dimension n), in
Bugaenko's format: one row per chamber root, with the dimensions n in which it is a wall.

Input (all in AlVin's chamber convention at v0 = e0: stabiliser walls -e_i + e_{i+1},
-e_n; every root of L_k padded with zeros is a vector of L_{k+1}):
  data/d1_roots_5.jsonl     AlVin chambers over Z[phi] (tools/d1_roots.py)
  data/d1_roots_ours.jsonl  our chambers (zphi/vinbergn.py; tools/d1_roots_ours.py) for
                            Q(sqrt13) and the Z[phi] forms AlVin does not finish in rank 3.
A root r (trailing zeros dropped) is listed once, with S(r) = {n : r padded is a wall of
the chamber of L_{n-2}}. The stabiliser family is listed as two rows.

Output: ../reflect-zphi-paper/sections/x13-roots.tex
"""
from __future__ import annotations

import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT.parent / "reflect-zphi-paper/sections/x13-roots.tex"


def el(x, D):
    a, b = x[0], x[1]
    den = x[2] if len(x) > 2 else 1
    g = r"\varphi" if D == 5 else r"\omega"
    if b == 0:
        s = str(a)
    else:
        t = g if b == 1 else (f"-{g}" if b == -1 else f"{b}{g}")
        s = t if a == 0 else f"{a}{'+' if b > 0 else ''}{t}"
    return s if den == 1 else rf"\tfrac{{{s}}}{{{den}}}"


def runs(entries):
    """Runs of >= 3 equal entries a written a^{(m)}."""
    out, i = [], 0
    while i < len(entries):
        j = i
        while j + 1 < len(entries) and entries[j + 1] == entries[i]:
            j += 1
        m = j - i + 1
        if m >= 3:
            e = entries[i]
            base = e if all(c.isalnum() or c == "\\" for c in e) else f"({e})"
            out.append(f"{base}^{{({m})}}")
        else:
            out += entries[i:j + 1]
        i = j + 1
    return ", ".join(out)


def strip(r):
    r = [tuple(x) for x in r]
    while len(r) > 1 and r[-1][0] == 0 and r[-1][1] == 0:
        r.pop()
    return tuple(r)


def is_stab(r):
    """-e_i + e_{i+1} or -e_n (x0 = 0, entries in {0, +-1})."""
    if tuple(r[0]) != (0, 0):
        return False
    nz = [(i, tuple(x)) for i, x in enumerate(r) if tuple(x) != (0, 0)]
    if len(nz) == 1 and nz[0][1] == (-1, 0):
        return True
    return (len(nz) == 2 and nz[0][1] == (-1, 0) and nz[1][1] == (1, 0)
            and nz[1][0] == nz[0][0] + 1)


def ranges(S, ntop):
    S = sorted(S)
    if S and S == list(range(S[0], ntop + 1)):
        return f"$n\\ge{S[0]}$" if len(S) > 1 else f"$n={S[0]}$"
    parts, i = [], 0
    while i < len(S):
        j = i
        while j + 1 < len(S) and S[j + 1] == S[j] + 1:
            j += 1
        parts.append(f"{S[i]}" if i == j else f"{S[i]}\\text{{--}}{S[j]}")
        i = j + 1
    if len(parts) == 1 and "--" not in parts[0]:
        return f"$n={parts[0]}$"
    return "$n\\in\\{" + ",".join(parts) + "\\}$"


def load():
    forms = {}
    for p in (ROOT / "data/d1_roots_5.jsonl", ROOT / "data/d1_roots_ours.jsonl"):
        if not p.exists():
            continue
        for line in open(p):
            r = json.loads(line)
            D = r.get("D", 5)
            if r.get("status", "reflective") != "reflective" or not r.get("roots"):
                continue
            if "ended" in r and not r["ended"]:
                continue
            src = "AlVin" if "ended" in r else "ours"
            key = (D, tuple(r["d"]))
            forms.setdefault(key, {})[r["k"]] = dict(roots=r["roots"], norms=r["norms"], src=src,
                                                       normalised=r.get("normalised", True))
    return forms


def kmax_alvin(D, d):
    for line in open(ROOT / f"data/d1_diag_{D}.jsonl"):
        r = json.loads(line)
        if r.get("final") and tuple(r["d"]) == tuple(d):
            return r["k_reflective_max"]
    return None


def table(D, d, ch):
    ks = sorted(ch)
    ntop = 2 + ks[-1]
    ka = kmax_alvin(D, d)
    missing = [] if ka is None else [k for k in range(ka + 1) if k not in ch]
    rows = {}
    for k in ks:
        for r, m in zip(ch[k]["roots"], ch[k]["norms"]):
            if is_stab(r):
                continue
            key = strip(r)
            rows.setdefault(key, [m, set()])[1].add(2 + k)
    def sortkey(item):
        r, (m, S) = item
        return (min(S), len(r), [abs(x[0]) + abs(x[1]) for x in r])
    srcs = sorted({ch[k]["src"] for k in ks})
    g = r"\varphi" if D == 5 else r"\omega"
    top = max([ntop] + [2 + k for k in missing])
    rng = "$n=2$" if top == 2 else f"$2\\le n\\le{top}$"
    out = [r"\begin{center}\footnotesize",
           r"\begin{tabular}{@{}lll@{}}",
           rf"\multicolumn{{3}}{{@{{}}l}}{{\normalsize $d={el(list(d), D)}$}}\\",
           rf"\multicolumn{{3}}{{@{{}}l}}{{reflective for {rng}; chambers: {', '.join(srcs)}}}\\[2pt]",
           r"\toprule", r"root $(x_0;x_1,\dots)$ & $(r,r)$ & $n$ \\", r"\midrule",
           r"$-e_i+e_{i+1}$, $1\le i<n$ & $2$ & all \\",
           r"$-e_n$ & $1$ & all \\"]
    for r, (m, S) in sorted(rows.items(), key=sortkey):
        coords = "; ".join([el(list(r[0]), D), runs([el(list(x), D) for x in r[1:]])]) if len(r) > 1 else el(list(r[0]), D)
        out.append(rf"$({coords})$ & ${el(m, D)}$ & {ranges(S, ntop)} \\")
    out += [r"\bottomrule", r"\end{tabular}"]
    if missing:
        dims = ", ".join(str(2 + k) for k in missing)
        out.append(r"\\[2pt]For $n=" + dims + r"$ the reflectivity is from AlVin; the chamber is not"
                   r" verified and its roots are not listed.")
    out += [r"\end{center}", r"\medskip", ""]
    bad = [k for k in ks if not ch[k]["normalised"]]
    if bad:
        out.insert(0, f"% WARNING: chambers for k in {bad} could not be normalised")
    return "\n".join(out)


def main():
    forms = load()
    out = ["% Generated by tools/d1_tables.py; do not edit.",
           r"\subsection{Root tables}\label{sec:d1-roots}",
           "For each reflective diagonal class we list the roots of the chamber of $L_k$ at",
           "$v_0=e_0$ for every reflective $k$, writing $n=2+k$ for the hyperbolic dimension.",
           "The chambers are normalised so that the stabiliser of $v_0$ contributes the walls",
           "$-e_i+e_{i+1}$ ($1\\le i<n$) and $-e_n$; every other wall then has",
           "$x_1\\ge\\dots\\ge x_n\\ge0$, and a root of $L_k$ padded with zeros is a vector of",
           "$L_{k+1}$. A root is written with its trailing zeros dropped, and the last column",
           "gives the dimensions $n$ in which (padded with zeros) it is a wall of the chamber;",
           "``$n\\ge a$'' means every $a\\le n\\le n_{\\max}$, with $n_{\\max}$ the largest",
           "dimension in which $L$ is known to be reflective. In a root, $a^{(m)}$ stands for",
           "$m$ consecutive coordinates equal to~$a$. A root is determined by its mirror only up",
           "to multiplication by a unit; we list the representatives of the program that computed",
           "the chamber (``AlVin'' or ``ours'' in the table header), and the norm column refers to",
           "that representative.", ""]
    for D in (5, 13):
        ring = r"\ZZ[\varphi]" if D == 5 else r"\ZZ[\omega]"
        out.append(rf"\subsubsection*{{Over ${ring}$}}")
        keys = sorted([k for k in forms if k[0] == D], key=lambda k: (-max(forms[k]), -k[1][1], k[1][0]))
        for key in keys:
            out.append(table(D, key[1], forms[key]))
    OUT.write_text("\n".join(out) + "\n")
    print(f"{sum(1 for _ in forms)} tables -> {OUT}")


if __name__ == "__main__":
    main()
