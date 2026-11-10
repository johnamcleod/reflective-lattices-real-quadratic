"""Gate A.3.2: Z[sqrt2] configuration counts = Mark's Table 1 'root configs'
column, rows (15) 282, (16) 1736, (22) 5777, (23) 88836, (27) 97526; and every
configuration equals Mark's printed matrix (15)/(16)/(22)/(23)/(27) exactly
(after the unit rescaling r' -> r'/u, s -> s/u documented in configs.mark_order).

Also records the Z[phi] counts (no published values; regression only)."""
import os
from collections import Counter

import pytest

from zphi import configs as C
from zphi.ring import ZS2, ZPHI

MARK_TABLE1 = {"15": 282, "16": 1736, "22": 5777, "23": 88836, "27": 97526}
ZPHI_COUNTS = {"15": 298, "16": 1636, "22": 2946, "23": 36961}


def _count(R, kind):
    cnt, bad = Counter(), 0
    for cfg in C.ENUMERATORS[kind](R):
        cnt[cfg.mark_type] += 1
        bad += C.scaled_gram(cfg) != C.mark_matrix(kind, cfg.key)
    return cnt, bad


@pytest.mark.gate2
def test_short_edge_zsqrt2():
    cnt, bad = _count(ZS2, "short_edge")
    assert cnt["15"] == MARK_TABLE1["15"] and cnt["16"] == MARK_TABLE1["16"]
    assert bad == 0


@pytest.mark.gate2
def test_short_edge_full_box_differs():
    """Without the Coxeter restriction at R∩T, R'∩T the counts are 360/1794
    (OPEN_QUESTIONS Q2): Mark's program must have imposed it."""
    cnt = Counter(cfg.mark_type for cfg in C.short_edge(ZS2, coxeter=False))
    assert (cnt["15"], cnt["16"]) == (360, 1794)


@pytest.mark.gate2
@pytest.mark.slow
def test_short_pair_zsqrt2():
    cnt, bad = _count(ZS2, "short_pair")
    assert cnt["22"] == MARK_TABLE1["22"] and cnt["23"] == MARK_TABLE1["23"]
    assert bad == 0


@pytest.mark.gate2
@pytest.mark.slow
def test_close_pair_zsqrt2():
    """Parallel over (A,B) slices (zphi.count_close); ~10 min on 8 cores."""
    from multiprocessing import Pool
    from zphi.count_close import run_slice, slices, CK
    import shutil
    shutil.rmtree(os.path.join(CK, "2"), ignore_errors=True)
    n = len(slices(ZS2))
    with Pool(os.cpu_count()) as pool:
        rs = pool.map(run_slice, [(2, i) for i in range(n)])
    assert sum(r["integral"] for r in rs) == MARK_TABLE1["27"]
    assert sum(r["ultraparallel"] for r in rs) == MARK_TABLE1["27"]
    assert sum(r["mark_mismatch"] for r in rs) == 0


@pytest.mark.slow
def test_zphi_regression_counts():
    se = Counter(cfg.mark_type for cfg in C.short_edge(ZPHI))
    sp = Counter(cfg.mark_type for cfg in C.short_pair(ZPHI))
    assert {**se, **sp} == ZPHI_COUNTS
