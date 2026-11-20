"""vinberg_diag against AlVin's chambers (data/d1_roots_5.jsonl), exact root sets."""
import json, sys, time
sys.path.insert(0, ".")
from zphi.ring import get_ring
from zphi.vinbergdiag import vinberg_diag
R = get_ring(5)
al = {(tuple(r["d"]), r["k"]): r for r in map(json.loads, open("data/d1_roots_5.jsonl"))}
cases = [tuple(map(int, a.split(","))) for a in sys.argv[1:]]
for a, b, k in cases:
    t0 = time.time()
    res = vinberg_diag(R(a, b), 2 + k, time_limit=3600)
    ours = {tuple(tuple(x.to_json()) for x in r) for r in res["roots"]}
    A = {tuple(tuple(x) for x in r) for r in al[((a, b), k)]["roots"]}
    print(json.dumps(dict(d=[a, b], k=k, status=res["status"], n=len(ours), n_alvin=len(A),
                          same=ours == A, secs=round(time.time() - t0, 1))), flush=True)
