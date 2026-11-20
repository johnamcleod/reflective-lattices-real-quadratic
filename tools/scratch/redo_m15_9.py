"""Redo the AlVin D1 run of <-(-15+9w),1,1,1> over Q(sqrt13) (k=1): the recorded run
(0.1 s, 1 root) was an AlVin segfault (rc 139), not an early stop. Prints the new record."""
import json, sys
sys.argv = ["x", "13"]
sys.path[:0] = ["tools", "."]
import d1_diagonal as DD
al = DD.run_alvin((-15, 9), 1)
print(json.dumps({x: al[x] for x in ("ended", "timed_out", "returncode", "crashes", "nroots", "secs",
                                     "signature", "says_nonreflective")}), flush=True)
