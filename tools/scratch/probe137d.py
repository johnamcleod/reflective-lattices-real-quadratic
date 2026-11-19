"""Class 137: per-norm node counts at vertex cells with the original enum_psi and with
enum_psi2 (solved O-coordinate from short trace-form vectors)."""
import json, sys, time
sys.path.insert(0, ".")
import tools.emit_sub as ES
import tools.sublat as SL
from tools.scratch.enum_psi2 import enum_psi2
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
orig = ES.enum_psi
for i in [int(x) for x in sys.argv[1:]]:
    A, B = P[i], P[i + 1]
    M = [a * (2 ** 20) + b for a, b in zip(A, B)]
    ES.enum_psi = orig
    t0 = time.time()
    cell = ES.make_cell_sub(R, G, [A, M], norms, bases, 10 ** 7)
    t1 = time.time()
    c0 = dict(V=cell["V"], pC=cell["pC"], qC=cell["qC"], mu=cell["mu"])
    ES.enum_psi = lambda R_, Psi, K, cap: enum_psi2(R_, Psi, K, cap)
    subs2 = [ES.subcell(R, G, c0, m, bases[j], 10 ** 7) for j, m in enumerate(norms)]
    t2 = time.time()
    print(i, "orig", cell["nodes"], [d["nodes"] for d in cell["subs"]], f"{t1-t0:.0f}s", flush=True)
    print(i, "new ", sum(d["nodes"] for d in subs2), [d["nodes"] for d in subs2], f"{t2-t1:.0f}s", flush=True)
