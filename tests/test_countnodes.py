"""The C node counter (tools/csrc/countnodes.c) agrees with the exact Python counter."""
import random

from tools import emit_polyenum as E
from tools.emit_cert import _clib, count_capped, count_capped_py


def _random_search(rng, big, scale=1):
    while True:
        M = [[rng.randint(-3, 3) for _ in range(6)] for _ in range(6)]
        F = [[x * scale for x in r] for r in E.matmul(E.transpose(M), M)]
        for i in range(6):
            F[i][i] += rng.randint(0, 3)
        try:
            a, w, S = E.ldl_int(F)
        except Exception:
            continue
        if all(w[i] > 0 and a[i][i] > 0 for i in range(6)):
            K = rng.randint(1, 40) * (10 ** 12 if big else 1)
            return a, w, S * K * scale


def test_c_counter_matches_python():
    assert _clib() is not None
    rng = random.Random(1)
    n = 0
    while n < 60:
        a, w, B = _random_search(rng, big=False)
        cap = rng.choice([50, 5000, 200000])
        ref = count_capped_py(a, w, B, cap)
        assert count_capped(a, w, B, cap) == ref
        n += 1


def test_c_counter_large_entries():
    """Class 95's searches have 100-bit a and 300-450-bit w, B."""
    rng = random.Random(2)
    for _ in range(15):
        a, w, B = _random_search(rng, big=False, scale=3 ** 200)
        assert max(x.bit_length() for x in w) > 128
        assert count_capped(a, w, B, 200000) == count_capped_py(a, w, B, 200000)


def test_c_path_taken(monkeypatch):
    import tools.emit_cert as EC
    def boom(*_):
        raise AssertionError("fell back to Python")
    monkeypatch.setattr(EC, "count_capped_py", boom)
    rng = random.Random(3)
    a, w, B = _random_search(rng, big=False, scale=7 ** 120)
    assert EC.count_capped(a, w, B, 10 ** 6) > 0
