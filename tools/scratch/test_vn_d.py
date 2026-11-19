import sys, time
sys.path.insert(0, ".")
from zphi.ring import get_ring
from zphi.linalg import bil
from zphi.vinbergn import vinberg_n
R = get_ring(5)
a, b = int(sys.argv[1]), int(sys.argv[2])
d = R(a, b)
for k in range(int(sys.argv[3]), int(sys.argv[4]) + 1):
    n = 3 + k
    G = [[(-d if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n)] for i in range(n)]
    v0 = [R.one] + [R.zero] * (n - 1)
    t = time.time()
    res = vinberg_n(G, v0, time_limit=1800)
    print(k, res["status"], len(res["roots"]), "start", res["n_start"], res.get("coxiter"),
          f"{time.time()-t:.1f}s", flush=True)
    for r in res["roots"]:
        print("   ", [str(x) for x in r], "norm", bil(G, r, r), flush=True)
    if res.get("graph"): print(res["graph"])
