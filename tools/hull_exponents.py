"""The module types of hull/(root lattice) that the candidate stage meets (paper Section 6.2).

    .venv/bin/python tools/hull_exponents.py [D ...]      (default: 2 5 13)

For every configuration key of the lattice stage (checkpoints/lat/<D>/<kind>/keys.jsonl),
rebuild the configuration, compute N0 = Hb^-1 Rb (zphi.lattices.hull_data) and its Smith
form, and record, for each prime p dividing an invariant factor, the exponent vector
e = (v_p(a_1), v_p(a_2), v_p(a_3)) that zphi.lattices.local_superlattices is called with.
Prints, per field, the number of configurations, the largest exponent seen, and a
histogram of (residue degree of p, sorted e). Writes logs/hull_exponents.json.
"""
from __future__ import annotations

import json
import os
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from zphi.configs import build  # noqa: E402
from zphi.lattices import hull_data, is_integral_mat, prime_list, snf, valuation  # noqa: E402
from zphi.ring import from_json, get_ring, ideal_eq  # noqa: E402

KINDS = ("short_edge", "short_pair", "close_pair")


def main(Ds):
    out = {}
    for D in Ds:
        R = get_ring(D)
        hist, n, skipped, emax = Counter(), 0, 0, 0
        for kind in KINDS:
            path = os.path.join(ROOT, "checkpoints", "lat", str(D), kind, "keys.jsonl")
            for line in open(path):
                cfg = build(kind, tuple(from_json(R, x) for x in json.loads(line)))
                n += 1
                _, _, N0 = hull_data(cfg.G, cfg.roots)
                if not is_integral_mat(N0):
                    skipped += 1        # roots not mutually crystallographic: no candidate
                    continue
                a = [snf(N0)[1][i][i] for i in range(3)]
                primes = []
                for ai in a:
                    for p in prime_list(ai):
                        if not any(ideal_eq(p, q) for q in primes):
                            primes.append(p)
                for p in primes:
                    e = tuple(sorted(valuation(ai, p) for ai in a))
                    q = abs(int(p.norm()))
                    deg = 1 if _rational_primes(q) else 2
                    hist[(deg, q, e)] += 1
                    emax = max(emax, max(e))
        out[D] = {"configurations": n, "not_crystallographic": skipped, "max_exponent": emax,
                  "types": {f"deg{d} N(p)={q} e={list(e)}": c
                            for (d, q, e), c in sorted(hist.items(), key=str)}}
        print(D, json.dumps(out[D], indent=1), flush=True)
    json.dump(out, open(os.path.join(ROOT, "logs", "hull_exponents.json"), "w"), indent=1)


def _rational_primes(n):
    """{n} if n is a rational prime, else {} (a prime of O of norm n is split/ramified iff
    its norm is prime; an inert prime has norm p^2)."""
    if n < 2:
        return set()
    k = 2
    while k * k <= n:
        if n % k == 0:
            return set()
        k += 1
    return {n}


if __name__ == "__main__":
    main([int(x) for x in sys.argv[1:]] or [2, 5, 13])
