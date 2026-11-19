"""Class 137: at the failing (depth-24) segment, per-norm counts for a wider mu grid and the
grouped counts with the groups choose_groups picks there."""
import json, sys, time
sys.path.insert(0, ".")
import tools.emit_sub as ES
from tools.b8_size import FILES
from tools.emit_cert import window, centre_real
from zphi.ring import get_ring, from_json
D, ci = 5, 137
R = get_ring(D)
c = json.load(open(FILES[D]))["classes"][ci]
G = [[from_json(R, e) for e in row] for row in c["gram"]]
u, uinv, p, q, Y, Sp, Dd = window(R, G)
norms = ES.E.window_norms(R, Dd, p, q, Y, Sp)
bases = [ES.sub_basis(R, G, m) for m in norms]
A = [R(-1694022, -2159554), R(232274711259, -143553700424), R(-7141410, 4290973)]
B = [R(-446725814, -722814722), R(1125275227, -706093408), R(-17123338, -27629051)]
pts = [A, B]
Vr, _ = centre_real(G, pts)
V, C2 = ES.E.centre_exact(R, G, pts, Vr)
pC, qC = C2.numerator, C2.denominator
VV = ES.bil(G, V, V)
rt = R.disc ** 0.5; wb = (R.c1 + rt) / 2
VV1, VV2 = float(VV), VV.sfloat()
print("qC", qC, "VV", VV, flush=True)
best = None
for fac in (0.05, 0.1, 0.2, 0.35, 0.5, 0.7, 1.0, 1.4, 2.0, 3.0, 5.0):
    target = max(fac * (2 * float(C2) - 1) * abs(VV1) * qC - qC * VV2, 1.5 * qC * VV2)
    y = -round(target / rt); x = round(-y * wb); mu = R(x, y)
    if not (abs(float(mu)) < qC * abs(VV1) and mu.sfloat() > qC * VV2):
        print("fac", fac, "mu out of range"); continue
    cc = dict(V=V, pC=pC, qC=qC, mu=mu)
    t0 = time.time()
    subs = [ES.subcell(R, G, cc, m, bases[i], 10 ** 7) for i, m in enumerate(norms)]
    tot = sum(d["nodes"] for d in subs)
    print("fac", fac, "total", tot, "max", max(d["nodes"] for d in subs), f"{time.time()-t0:.0f}s", flush=True)
    if best is None or tot < best[0]:
        best = (tot, dict(cc, nodes=tot, subs=subs))
groups = ES.choose_groups(R, G, best[1], norms, bases)
print("groups", groups, flush=True)
print("grouped", [ES.subcell_group(R, G, best[1], norms, bases, g)["nodes"] for g in groups], flush=True)
