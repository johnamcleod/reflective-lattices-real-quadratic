"""Arithmetic Coxeter triangles with Vinberg field Q(sqrt5) / Q(sqrt2) (exact).

Expected Q(sqrt5) lists: TASK.md (Takeuchi, J. Math. Soc. Japan 29 (1977), read
secondhand; the original could not be fetched, see OPEN_QUESTIONS.md). The
computation in zphi.triangles is independent of that list.
"""
from zphi.ring import get_ring
from zphi.triangles import vinberg_field_triangles, triangle_data

ZPHI_ARITH = [(2, 3, 10), (2, 4, 5), (2, 4, 10), (2, 5, 5), (2, 5, 6), (2, 5, 10),
              (2, 10, 10), (3, 3, 5), (3, 5, 5), (4, 4, 5), (5, 5, 5), (5, 10, 10)]
ZPHI_NONARITH = [(2, 6, 10), (3, 10, 10), (5, 6, 6)]
ZSQRT2_ARITH = [(2, 3, 8), (2, 4, 8), (2, 6, 8), (2, 8, 8), (3, 3, 4), (3, 8, 8),
                (4, 4, 4), (4, 6, 6), (4, 8, 8)]


def test_zphi_triangles():
    t = vinberg_field_triangles(get_ring(5))
    assert [tuple(x) for x in t["arithmetic"]] == ZPHI_ARITH
    assert [tuple(x) for x in t["non_arithmetic"]] == ZPHI_NONARITH


def test_zsqrt2_triangles():
    t = vinberg_field_triangles(get_ring(2))
    assert [tuple(x) for x in t["arithmetic"]] == ZSQRT2_ARITH
    assert t["non_arithmetic"] == []


def test_rational_field_excluded():
    # (3,4,4): all cyclic products rational, Vinberg field Q, not Q(sqrt2)
    assert not triangle_data(get_ring(2), 3, 4, 4)["field_is_K"]
    # (2,3,7): gamma(7) not in Z[phi]
    assert 7 not in get_ring(5).gammas
