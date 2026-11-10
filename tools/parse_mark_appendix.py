"""Parse Mark's appendix (arXiv:1512.01133, Appendix B, Tables 3-...) into
data/mark_zsqrt2_432.json, validating every entry exactly.

    python tools/parse_mark_appendix.py papers/mark_1512.01133.txt

The input is `pdftotext -layout` output. Each entry is:
    det = <delta>      det norm = <N>
    <angle sequence>                      e.g. 824, (22228222)2
    quadratic form   + 3 rows of 6 integers (pairs (a b) = a + b sqrt2)
    root list / roots norms
    r1 <6 ints> <2 ints>  ...
Validation per entry: symmetric Gram; det(G) = delta exactly; N(delta) = printed
norm; every printed root has the printed norm and is a root (primitive, 2Gr/r^2
integral); consecutive roots form the printed angles (4cos^2(pi/m)) and the chain
closes. Any failure is reported, never silently skipped.
"""
from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.ring import ZS2, gcd_list  # noqa: E402
from zphi.linalg import det, bil, mat_vec  # noqa: E402
from zphi.boxes import gammas  # noqa: E402

R = ZS2
INT = re.compile(r"[−-]?\d+")


def ints(line):
    return [int(t.replace("−", "-")) for t in INT.findall(line)]


def parse_det(s):
    """'1 − w', '−24 − 17w', '−3w', '5' -> El."""
    s = s.replace("−", "-").replace(" ", "")
    m = re.fullmatch(r"([+-]?\d+)?(?:([+-])(\d*)w)?|([+-]?\d*)w", s)
    if not m:
        raise ValueError(s)
    if m.group(4) is not None:
        b = m.group(4)
        b = int(b + "1") if b in ("", "+", "-") else int(b)
        return R(0, b)
    a = int(m.group(1)) if m.group(1) else 0
    b = 0
    if m.group(2):
        b = int(m.group(3)) if m.group(3) else 1
        if m.group(2) == "-":
            b = -b
    return R(a, b)


def parse(path):
    lines = open(path, encoding="utf-8").read().split("\n")
    start = next(i for i, l in enumerate(lines) if "Appendix B. Tables" in l)
    entries = []
    table = None
    i = start
    while i < len(lines):
        l = lines[i]
        mt = re.search(r"Table (\d+): (\w+)", l)
        if mt:
            table = mt.group(2)
        md = re.search(r"det\s*=\s*(.+?)\s+det norm\s*=\s*([−-]?\d+)", l)
        if not md:
            i += 1
            continue
        e = {"table": table, "line": i + 1, "det_text": md.group(1).strip(),
             "det_norm": int(md.group(2).replace("−", "-"))}
        i += 1
        while not lines[i].strip():
            i += 1
        t = lines[i].strip()
        if re.fullmatch(r"\d", t):
            # superscript exponent on its own line, then "(seq)"
            j = i + 1
            while not lines[j].strip():
                j += 1
            nxt = lines[j].strip()
            if re.fullmatch(r"\(\d+\)", nxt):
                t = nxt + t
                i = j
        e["angles_text"] = t
        while "quadratic form" not in lines[i]:
            i += 1
        i += 1
        rows = []
        while len(rows) < 3:
            v = ints(lines[i])
            if len(v) >= 6:
                rows.append(v[:6])
            i += 1
        e["gram_raw"] = rows
        while "root list" not in lines[i]:
            i += 1
        i += 1
        roots = []
        while i < len(lines):
            l = lines[i]
            if re.search(r"det\s*=", l) or re.search(r"Table \d+:", l):
                break
            m = re.match(r"\s*r(\d+)\s+(.*)", l)
            if m:
                v = ints(m.group(2))
                if len(v) != 8:
                    raise ValueError(f"line {i+1}: root row has {len(v)} ints: {l!r}")
                roots.append((int(m.group(1)), v))
            i += 1
        e["roots_raw"] = roots
        entries.append(e)
    return entries


def angle_seq(text):
    """'824' -> [8,2,4]; '(22228222)2' -> repeated twice. Digits are angle orders,
    except '1' which never occurs alone (10 does not occur over Z[sqrt2])."""
    t = text.replace(" ", "")
    m = re.fullmatch(r"\((\d+)\)(\d)", t)
    if m:
        return [int(c) for c in m.group(1)] * int(m.group(2))
    if not re.fullmatch(r"\d+", t):
        raise ValueError(text)
    return [int(c) for c in t]


def validate(e):
    G = [[R(e["gram_raw"][i][2 * j], e["gram_raw"][i][2 * j + 1]) for j in range(3)]
         for i in range(3)]
    issues = []
    if any(G[i][j] != G[j][i] for i in range(3) for j in range(3)):
        issues.append("not symmetric")
    delta = parse_det(e["det_text"])
    d = det(G)
    if d != delta:
        issues.append(f"det(G) = {d} != printed {delta}")
    if delta.norm_num() != e["det_norm"]:
        issues.append(f"N(delta) = {delta.norm_num()} != printed {e['det_norm']}")
    roots, norms = [], []
    for idx, v in e["roots_raw"]:
        r = [R(v[0], v[1]), R(v[2], v[3]), R(v[4], v[5])]
        n = R(v[6], v[7])
        roots.append(r)
        norms.append(n)
        if bil(G, r, r) != n:
            issues.append(f"r{idx}: norm {bil(G, r, r)} != printed {n}")
        elif not (n.tpos() and gcd_list(r, R).is_unit()
                  and all((2 * x / n).is_integral() for x in mat_vec(G, r))):
            issues.append(f"r{idx} is not a root")
    try:
        ang = angle_seq(e["angles_text"])
    except ValueError:
        ang = None
        issues.append(f"cannot parse angles {e['angles_text']!r}")
    gam = gammas(R)
    k = len(roots)
    sym = re.fullmatch(r"\((\d+)\)(\d)", e["angles_text"].replace(" ", ""))
    e["symmetry_order"] = int(sym.group(2)) if sym else 1
    if sym:
        # only one period of roots is listed: an open chain r1..rk with the
        # first k-1 angles of the period (the last angle joins rk to the image of r1)
        period = [int(c) for c in sym.group(1)]
        if len(period) != k:
            issues.append(f"period {len(period)} but {k} roots")
        else:
            for i in range(k - 1):
                x, y = roots[i], roots[i + 1]
                c = 4 * bil(G, x, y) ** 2 / (bil(G, x, x) * bil(G, y, y))
                if bil(G, x, y).sign() > 0 or c != gam[period[i]]:
                    issues.append(f"angle r{i+1},r{i+2}: 4cos^2 = {c}, printed pi/{period[i]}")
    elif ang is not None and len(ang) != k:
        issues.append(f"{len(ang)} angles but {k} roots")
    elif ang is not None:
        for i in range(k):
            x, y = roots[i], roots[(i + 1) % k]
            c = 4 * bil(G, x, y) ** 2 / (bil(G, x, x) * bil(G, y, y))
            m = ang[i]
            if bil(G, x, y).sign() > 0 or c != gam[m]:
                issues.append(f"angle r{i+1},r{(i+1)%k+1}: 4cos^2 = {c}, printed pi/{m}")
    e["gram"] = [[x.to_json() for x in row] for row in G]
    e["roots"] = [[x.to_json() for x in r] for r in roots]
    e["norms"] = [n.to_json() for n in norms]
    e["det"] = delta.to_json()
    e["angles"] = ang
    e["issues"] = issues
    return e


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "papers", "mark_1512.01133.txt")
    entries = [validate(e) for e in parse(path)]
    for e in entries:
        del e["gram_raw"], e["roots_raw"]
    from collections import Counter
    print("entries:", len(entries), dict(Counter(e["table"] for e in entries)))
    bad = [e for e in entries if e["issues"]]
    print("entries with issues:", len(bad))
    for e in bad[:30]:
        print(" line", e["line"], e["table"], e["det_text"], e["issues"][:3])
    out = os.path.join(ROOT, "data", "mark_zsqrt2_432.json")
    with open(out, "w") as f:
        json.dump(entries, f, indent=1)
    print("wrote", out)


if __name__ == "__main__":
    main()
