"""Re-verify the polygon certificates of all of Mark's appendix entries
(data/mark_check.json) with the current check_polygon."""
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from zphi.ring import ZS2 as R, from_json  # noqa: E402
from zphi.vinberg import check_polygon  # noqa: E402

E = json.load(open(os.path.join(ROOT, "data", "mark_zsqrt2_432.json")))


def one(c):
    G = [[from_json(R, x) for x in row] for row in E[c["idx"]]["gram"]]
    rts = [[from_json(R, x) for x in r] for r in c["roots"]]
    try:
        return c["idx"], check_polygon(G, [rts[k] for k in c["cycle"]])["ok"]
    except Exception as ex:
        return c["idx"], repr(ex)


if __name__ == "__main__":
    C = json.load(open(os.path.join(ROOT, "data", "mark_check.json")))["entries"]
    with Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 8) as p:
        res = list(p.imap_unordered(one, C, chunksize=1))
    print(json.dumps({"n": len(res), "ok": dict(Counter(str(v) for _, v in res)),
                      "bad": [i for i, v in res if v is not True][:20]}))
