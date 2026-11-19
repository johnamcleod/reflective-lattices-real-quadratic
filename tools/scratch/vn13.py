import sys, time, json
sys.path.insert(0, ".")
from zphi.ring import get_ring
from zphi.linalg import bil
from zphi.vinbergn import vinberg_n
R = get_ring(13)
for (a, b, k) in [(0, 1, 1), (-2, 1, 1), (-2, 1, 2)]:
    d = R(a, b); n = 3 + k
    G = [[(-d if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n)] for i in range(n)]
    v0 = [R.one] + [R.zero] * (n - 1)
    t = time.time()
    res = vinberg_n(G, v0, time_limit=3600)
    rec = dict(D=13, d=[a, b], k=k, status=res["status"], nroots=len(res["roots"]),
               coxiter=res.get("coxiter"), secs=round(time.time() - t, 1),
               roots=[[x.to_json() for x in r] for r in res["roots"]],
               norms=[bil(G, r, r).to_json() for r in res["roots"]], graph=res.get("graph"))
    print(json.dumps(rec), flush=True)
