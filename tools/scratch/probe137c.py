"""Class 137: per-vertex cell sizes at a fixed small radius, to locate the bad region, and
the mu/K/VV data of a good and a bad cell."""
import json, sys
from math import sqrt, acosh
sys.path.insert(0, ".")
import tools.emit_sub as ES
from tools.b8_size import FILES
from tools.emit_cert import polygon_data, window
from zphi.ring import get_ring, from_json
from zphi.linalg import bil
R = get_ring(5)
c = json.load(open(FILES[5]))["classes"][137]
G = [[from_json(R, e) for e in row] for row in c["gram"]]
roots = [[from_json(R, e) for e in r] for r in c["polygon"]["roots"]]
rs, P, f_, Xs, cf = polygon_data(R, G, roots)
u, uinv, p, q, Y, Sp, Dd = window(R, G)
norms = ES.E.window_norms(R, Dd, p, q, Y, Sp)
bases = [ES.sub_basis(R, G, m) for m in norms]
f = lambda a, b: float(bil(G, a, b))
print("norms", [str(m) for m in norms])
print("n points", len(P))
for i in range(len(P) - 1):
    A, B = P[i], P[i + 1]
    ch = f(A, B) / sqrt(f(A, A) * f(B, B))
    print(i, "edge length", f"{acosh(abs(ch)):.4f}", "max |coord| A", f"{max(abs(float(x)) for x in A):.3g}", flush=True)
# tiny segments at each vertex: A and a point very close to it along the edge
import fractions
for i in range(len(P) - 1):
    A, B = P[i], P[i + 1]
    # point M = A + t B, small t, scaled to integers
    t = 1
    while True:
        M = [a * (2 ** 20) * t + b for a, b in zip(A, B)]  # close to A
        if f(M, M) < 0: break
        t *= 2
    try:
        cell = ES.make_cell_sub(R, G, [A, M], norms, bases, 10 ** 7)
    except Exception as e:
        print(i, "err", e); continue
    if cell is None:
        print(i, "cell None"); continue
    print(i, "vertex cell nodes", cell["nodes"], "C2", cell["pC"] / cell["qC"],
          "per-norm max", max(d["nodes"] for d in cell["subs"]), flush=True)
