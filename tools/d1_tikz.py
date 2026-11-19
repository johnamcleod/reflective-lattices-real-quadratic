"""TikZ Coxeter diagrams of the reflective L_k = <-d, 1^(2+k)>, k >= 1 (D1), for the manuscript.

Input: the CoxIter graphs data/d1_graphs_{D}/d{a}_{b}_k{k}.coxiter (one line "i j w" per pair
that is not orthogonal: w = m for angle pi/m, 0 parallel, 1 ultraparallel). For D = 13 the
graphs come from our own Vinberg run (logs/vn13.jsonl, zphi/vinbergn.py) when present, since
AlVin's Q(sqrt13) polytopes may belong to a reflection subgroup (DISCREPANCIES #7).

Drawing convention (standard): no edge = orthogonal; plain edge = pi/3; edge labelled m =
pi/m (m >= 4); bold edge = parallel; dotted edge = ultraparallel.

Layout: a spring embedding (floats; the layout carries no mathematical content), the best
of several seeds by number of crossings of non-dotted edges. Deterministic.

Usage: .venv/bin/python tools/d1_tikz.py  ->  ../reflect-zphi-paper/sections/x13-diagrams.tex
"""
from __future__ import annotations

import json
import pathlib
import re

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT.parent / "reflect-zphi-paper/sections/x13-diagrams.tex"


def parse(text):
    lines = text.strip().splitlines()
    n = int(lines[0].split()[0])
    edges = []
    for line in lines[2:]:
        i, j, w = map(int, line.split())
        edges.append((i - 1, j - 1, w))
    return n, edges


def crossings(P, edges):
    E = [(i, j) for i, j, w in edges if w != 1]

    def ccw(a, b, c):
        return (c[1] - a[1]) * (b[0] - a[0]) - (b[1] - a[1]) * (c[0] - a[0])

    cnt = 0
    for x in range(len(E)):
        for y in range(x + 1, len(E)):
            a, b = E[x]
            c, d = E[y]
            if len({a, b, c, d}) < 4:
                continue
            A, B, C, D = P[a], P[b], P[c], P[d]
            if (ccw(A, B, C) * ccw(A, B, D) < 0) and (ccw(C, D, A) * ccw(C, D, B) < 0):
                cnt += 1
    return cnt


def spring(n, edges, seed, iters=300):
    """Stress majorization (SMACOF) on graph distances: solid edges length 1, dotted 2."""
    INF = 10 ** 9
    Dm = np.full((n, n), float(INF))
    np.fill_diagonal(Dm, 0)
    for i, j, w in edges:
        L = 2.0 if w == 1 else 1.0
        Dm[i, j] = Dm[j, i] = min(Dm[i, j], L)
    for k in range(n):
        Dm = np.minimum(Dm, Dm[:, k:k + 1] + Dm[k:k + 1, :])
    fin = Dm[Dm < INF]
    Dm[Dm >= INF] = fin.max() + 1
    Wt = np.divide(1.0, Dm ** 2, out=np.zeros_like(Dm), where=Dm > 0)
    rng = np.random.default_rng(seed)
    X = rng.uniform(-1, 1, size=(n, 2)) * Dm.max()
    V = -Wt.copy()
    np.fill_diagonal(V, Wt.sum(axis=1))
    Vp = np.linalg.pinv(V)
    for _ in range(iters):
        E = np.linalg.norm(X[:, None] - X[None], axis=2)
        Bm = np.where(E > 1e-9, -Wt * Dm / np.maximum(E, 1e-9), 0)
        np.fill_diagonal(Bm, 0)
        np.fill_diagonal(Bm, -Bm.sum(axis=1))
        X = Vp @ Bm @ X
    X -= X.mean(axis=0)
    return X


def layout(n, edges):
    best = None
    for seed in range(24):
        P = spring(n, edges, seed)
        c = crossings(P, edges)
        if best is None or c < best[0]:
            best = (c, P)
    P = best[1]
    span = max(np.ptp(P[:, 0]), np.ptp(P[:, 1]), 1e-9)
    width = 3.0 if n <= 6 else (4.5 if n <= 12 else 7.5)
    return P * (width / span)


def tikz(n, edges):
    P = layout(n, edges)
    out = [r"\begin{tikzpicture}[v/.style={circle,draw,fill=white,inner sep=0pt,minimum size=5pt}]"]
    for i in range(n):
        out.append(rf"\node[v] (n{i}) at ({P[i,0]:.2f},{P[i,1]:.2f}) {{}};")
    for i, j, w in edges:
        if w == 1:
            out.append(rf"\draw[densely dotted,gray] (n{i}) -- (n{j});")
    for i, j, w in edges:
        if w == 0:
            out.append(rf"\draw[line width=1.6pt] (n{i}) -- (n{j});")
        elif w == 3:
            out.append(rf"\draw (n{i}) -- (n{j});")
        elif w >= 4:
            out.append(rf"\draw (n{i}) -- node[fill=white,inner sep=0.5pt,font=\scriptsize] {{{w}}} (n{j});")
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


def fmt_d(D, a, b):
    g = r"\varphi" if D == 5 else r"\omega"
    if b == 0:
        return str(a)
    t = (g if b == 1 else (f"-{g}" if b == -1 else f"{b}{g}"))
    if a == 0:
        return t
    return f"{a}{'+' if b > 0 else ''}{t}"


def main():
    items = []
    for D in (5, 13):
        ours = {}
        p = ROOT / "logs/vn13.jsonl"
        if D == 13 and p.exists():
            for line in open(p):
                r = json.loads(line)
                if r["status"] == "reflective":
                    ours[(tuple(r["d"]), r["k"])] = r["graph"]
        for f in sorted((ROOT / f"data/d1_graphs_{D}").glob("*.coxiter")):
            a, b, k = map(int, re.match(r"d(-?\d+)_(-?\d+)_k(\d+)", f.stem).groups())
            if k < 1:
                continue
            src = "AlVin"
            text = f.read_text()
            if (a, b) in [x[0] for x in ours] and ((a, b), k) in ours:
                text, src = ours[((a, b), k)], "ours"
            n, edges = parse(text)
            items.append(dict(D=D, a=a, b=b, k=k, n=n, edges=edges, src=src))
    items.sort(key=lambda x: (x["D"], -x["b"], x["a"], x["k"]))
    out = [
        "% Generated by tools/d1_tikz.py from data/d1_graphs_{D}/ (and logs/vn13.jsonl); do not edit.",
        r"\subsection{Coxeter diagrams}\label{sec:d1-diagrams}",
        "For every reflective $L_k$ with $k\\ge1$ we give the Coxeter diagram of its chamber.",
        "Convention: no edge means orthogonal mirrors; a plain edge, angle $\\pi/3$; an edge",
        "labelled~$m$, angle $\\pi/m$; a dotted edge, ultraparallel mirrors (no two mirrors are",
        "parallel, since every polytope is compact). Each caption gives $d$, $k$, the rank",
        "$3+k$ and the number of walls.",
        "",
    ]
    for D in (5, 13):
        group = [x for x in items if x["D"] == D]
        ring = r"\ZZ[\varphi]" if D == 5 else r"\ZZ[\omega]"
        out.append(rf"\subsubsection*{{Over ${ring}$}}")
        if D == 13:
            nv = sum(1 for x in group if x["src"] == "ours")
            out.append(
                "These diagrams are those of the chambers found by our own implementation "
                "(stage~2) where it has finished" + (f" ({nv} of {len(group)})" if nv < len(group) else "")
                + "; AlVin's polytopes over this ring may belong to a reflection subgroup "
                "(DISCREPANCIES~\\#7)." if nv else
                "\\textbf{Unverified:} these are AlVin's polytopes, which over this ring may "
                "belong to a proper reflection subgroup (DISCREPANCIES~\\#7); the chamber check "
                "by our own implementation is running.")
            out.append("")
        col = 0
        for x in group:
            cap = (f"$d={fmt_d(D, x['a'], x['b'])}$, $k={x['k']}$ (rank ${3 + x['k']}$), "
                   f"{x['n']} walls" + ("" if D == 5 else f" [{x['src']}]"))
            wide = x["n"] > 12
            if wide and col:
                out.append(r"\par\medskip")
                col = 0
            w = r"\textwidth" if wide else r"0.48\textwidth"
            out.append(r"\noindent\begin{minipage}[b]{" + w + r"}\centering")
            out.append(tikz(x["n"], x["edges"]))
            out.append(r"\par\smallskip{\small " + cap + r"}\end{minipage}")
            if wide:
                out.append(r"\par\medskip")
            elif col == 0:
                out.append(r"\hfill")
                col = 1
            else:
                out.append(r"\par\medskip")
                col = 0
        if col:
            out.append(r"\par\medskip")
    OUT.write_text("\n".join(out) + "\n")
    print(f"{len(items)} diagrams -> {OUT}")


if __name__ == "__main__":
    main()
