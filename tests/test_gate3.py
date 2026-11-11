"""Gate A.3.3: Z[sqrt2] lattice stage (short edges recomputed here; the pair types are
checked against the checkpointed run when it is present).

Expected values are OUR counts (explained against Mark's Table 1 in DISCREPANCIES #3):
the SSF column matches Mark's 130/341 only up to the hull definition, and Mark's
column is taken before the local-simplicity filter.
"""
import os
from collections import Counter
from multiprocessing import Pool

import pytest

from zphi.configs import ENUMERATORS
from zphi.ring import ZS2
from zphi import run_lattices

pytestmark = [pytest.mark.gate3, pytest.mark.slow]

EXPECTED_SHORT_EDGE = {
    "15": {"configs": 282, "enlargements": 1998, "ssf": 134, "ssf_locally_simple": 77},
    "16": {"configs": 1736, "enlargements": 9351, "ssf": 351, "ssf_locally_simple": 286},
}


def _one(kj):
    rec = run_lattices.process_key(2, "short_edge", kj)
    return rec["type"], rec["enlargements"], len(rec["lattices"]), \
        sum(L["locally_simple"] for L in rec["lattices"])


def test_short_edge_lattice_stage():
    keys = [c.key_json() for c in ENUMERATORS["short_edge"](ZS2)]
    out = {}
    with Pool(os.cpu_count()) as pool:
        for t, e, s, ls in pool.imap_unordered(_one, keys, chunksize=8):
            c = out.setdefault(t, Counter())
            c["configs"] += 1
            c["enlargements"] += e
            c["ssf"] += s
            c["ssf_locally_simple"] += ls
    assert {k: dict(v) for k, v in out.items()} == EXPECTED_SHORT_EDGE


def test_checkpointed_summary_consistent():
    """If the full run exists, its per-type config counts equal Table 1."""
    table1 = {"15": 282, "16": 1736, "22": 5777, "23": 88836, "27": 97526}
    for kind in ("short_edge", "short_pair", "close_pair"):
        d = run_lattices._dir(2, kind)
        if not os.path.isdir(d):
            continue
        s = run_lattices.summary(2, kind)
        for t, v in s.items():
            assert v["configs"] == table1[t]
            assert v["ssf_locally_simple"] <= v["ssf"] <= v["enlargements"]
