"""Class 137: at the failing segment, does centre_exact reach its tolerance? (C2 vs the real
optimum target, and the scale used.)"""
import json, sys
from math import sqrt
sys.path.insert(0, ".")
import tools.emit_sub as ES
from tools.b8_size import FILES
from tools.emit_cert import centre_real
from zphi.ring import get_ring, from_json
from zphi.linalg import bil
R = get_ring(5)
c = json.load(open(FILES[5]))["classes"][137]
G = [[from_json(R, e) for e in row] for row in c["gram"]]
A = [R(-1694022, -2159554), R(232274711259, -143553700424), R(-7141410, 4290973)]
B = [R(-446725814, -722814722), R(1125275227, -706093408), R(-17123338, -27629051)]
pts = [A, B]
f = lambda u, v: float(bil(G, u, v))
print("real coords A", [float(x) for x in A], "conj", [x.sfloat() for x in A])
print("cosh(A,B)^2", f(A, B) ** 2 / (f(A, A) * f(B, B)))
Vr, _ = centre_real(G, pts)
target = max((-sum(float(G[i][j]) * Vr[i] * float(p[j]) for i in range(3) for j in range(3)) / sqrt(-f(p, p))) ** 2 for p in pts)
print("Vr", Vr, "target C2", target)
rt = sqrt(R.disc); wb, wc = (R.c1 + rt) / 2, (R.c1 - rt) / 2
scale = 4
while scale < 2 ** 40:
    V = [R(round(-t * scale * wc / (wb - wc)), round(t * scale / (wb - wc))) for t in Vr]
    VV = bil(G, V, V)
    if float(VV) < 0 and all(f(V, p) < 0 for p in pts):
        C2 = max(f(V, p) ** 2 / (float(VV) * f(p, p)) for p in pts)
        print(f"scale 2^{scale.bit_length()-1}: C2 {C2:.6g}")
    scale *= 2
print("G", [[str(x) for x in r] for r in G])
print("roots", c["polygon"]["roots"][:4], "...", len(c["polygon"]["roots"]))
