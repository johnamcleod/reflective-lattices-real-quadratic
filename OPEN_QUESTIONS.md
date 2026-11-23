# Open questions

Each entry gives its status and how it will be resolved. None of these is assumed away.

## Q1. Close-pair conditions: Mark's γ-test vs the prototype. RESOLVED (10 Nov 2026)

- **Equivalence.** Mark's (25) are exactly the root conditions 2(s·s′)/s² ∈ o and 2(s·s′)/s′² ∈ o, because s² = 2A′BN/k² and s′² = 2AB′N′/k′² at her scale.
- **Exact agreement.** Over ℤ[√2], all 97526 configurations passing these conditions agree entry by entry with Mark's printed (27), including the closed-form γ of (26).
- **The extra filter is inert.** The prototype's ultraparallel filter (s·s′ < 0 and (s·s′)² > s²s′²) removes **none** of them, so the count is 97526 with or without it.
- `tests/test_configs.py::test_close_pair_zsqrt2`.

## Q2. Coxeter restriction in Lemma 9. CONFIRMED, recorded in DISCREPANCIES #1

- Our code reproduces the prototype's finding: with the printed full box 0 < AB, A′B′ < 4 the counts are 360/1794; with AB, A′B′ ∈ {4cos²(π/m)} they are 282/1736, which is Mark's Table 1.
- **Geometric justification.** R∩T and R′∩T are vertices of a Coxeter polygon.
- The same restriction applies to A′B′ in Lemma 10. The (22)/(23) counts 5777/88836 match with it.
- `tests/test_configs.py::test_short_edge_full_box_differs`.

## Q3. Lattice-stage counts versus Mark's Table 1 (gate A.3.3)

- **Original form:** short-edge lattices 134/351 against Mark's 130/341.
- **Tested hypotheses:**
  1. *Local simplicity removes the excess.* No. Our filter (Mark §2.8(3): at each configuration vertex of angle π/m the lattice has exactly m mirrors) cuts the short-edge SSF counts 134 → 77 and 351 → 286, which is far below 130/341. For type (23) the post-filter count 1190 is nearer 1096 than the pre-filter 1262. So we cannot tell whether Mark's "squarefree enlargements" column is taken before or after her local-simplicity removal. Her §3.5 sentence order suggests before.
  2. *Hull over all roots of R (Mark §2.9).* It does not reproduce her numbers either; see DISCREPANCIES #3.
- **Status:** open. Our enumeration is a provable superset of the lattices in which the configuration vectors are roots, so completeness does not depend on resolving this. **It is not assumed away:** gate A.3.4 compares the final reflective lists. Any lattice we find that is reflective, SSF and missing from Mark's 432 would be a substantive discrepancy, to be reported.
- Mark's text also says her enumeration had redundancies ("large overestimates"), so her counts are not canonical invariants. Item-by-item reproduction is not possible without her program.

## Q4. Missing companion files

- `qsqrt5.py`, `step1_compute.py`, `corner_check.py` and `step1_results.json` were not supplied.
- **User decision:** re-derive their checks as tests, using the numbers in `notes/step1-zphi-lemmas.md` as expected values.

## Q5. Secondhand data to verify against sources

- **Takeuchi's ℚ(√5) triangles and their commensurability classes:** fetch J. Math. Soc. Japan 29 (1977), and also Takeuchi, J. Fac. Sci. Univ. Tokyo 24 (1977) for the commensurability classes.
  - *2026-11-13:* automatic fetch failed (J-STAGE 404; Project Euclid returns HTML, not the PDF). The user needs to supply the PDF.
  - Independent exact recomputation (`zphi/triangles.py`, Vinberg's criterion; `tests/test_triangles.py`) reproduces the twelve arithmetic triangles and the three non-arithmetic ones with Vinberg field ℚ(√5) exactly as listed in TASK.md. Over ℚ(√2) it gives 9 arithmetic triangles.
  - The comparison with the source itself is still open.
  - **RESOLVED 2026-11-13 (`tools/triangle_lattices.py`, `data/triangles_5.json`).** All twelve triangles occur as configurations with SSF lattices in which the three roots are roots (25 lattices in all). Each such lattice is reflective, with a certified chamber matched to one of our 144 classes by explicit isometry:
    - (2,3,10), (2,4,5), (2,4,10) and (2,5,6): the chamber is the triangle itself (locally simple).
    - The other eight fail local simplicity, so the full reflection group is strictly larger:
      - (2,5,5) ⊂ (2,4,5);
      - (3,3,5), (5,5,5), (2,5,10) ⊂ (2,3,10);
      - (2,10,10), (4,4,5), (5,10,10) ⊂ (2,4,10);
      - (3,5,5) ⊂ (2,5,6).
    - Each containment is a known triangle-group inclusion (Singerman 1972), e.g. (s,s,t) < (2,s,2t) and (2,n,2n) < (2,3,2n).
    - So the "lattices realising the twelve triangles" all appear in the final list. Only four triangles are chambers of SSF lattices.
  - **Commensurability classes (from the certified containments):**
    - {(2,3,10), (3,3,5), (5,5,5), (2,5,10)};
    - {(2,4,5), (2,5,5), (2,4,10), (2,10,10), (4,4,5), (5,10,10)};
    - {(2,5,6), (3,5,5)}.

    This differs from the step-1 notes' recollection of Takeuchi in two places, (2,5,5) and (2,5,10); see DISCREPANCIES #6. A check against Takeuchi's paper is still pending (PDF needed).
  - **Update 2026-11-23:** Nagano–Shiga, arXiv:1511.02941v5, Table App 1, reproduces Takeuchi's list with class labels: VI = (2,4,5), (2,4,10), (2,5,5), (2,10,10), (4,4,5), (5,10,10); VII = (2,5,6), (3,5,5); VIII = (2,3,10), (2,5,10), (3,3,5), (5,5,5), all over ℚ(√5). This is exactly our grouping, and the paper now cites it alongside Takeuchi. Takeuchi's original itself has still not been read.
- **Guglielmetti's ⟨−√5,1,1⟩ and ⟨−φ,2+φ,1⟩:** fetch the thesis.
- **Bugaenko's ⟨−φ,1,1⟩:** primary source probably unavailable; also check by computation.
- **Mcleod thesis §3.2:** a copy is in the sibling project.

## Q6. The H₂ glue-sign lemma (the analogue of Mark's Lemmas 6–7)

- This must be proved before walking can use H₂ glue signs. Until then, walking uses A₂ signs only, and Vinberg is used everywhere else.
- **Status (2026-11-23):** not needed. No result depends on it (the walk is a search heuristic; every decision is a certificate), and the manuscript does not claim it.

## Q7. Step-1 §4.1 for A₁² corners

- The claim that "b is a unit" is unproven for right-angled corners (step-1 §9 item 4). Not needed by the pipeline, which handles A₁² generically, but the manuscript must not claim it.
- **Status (2026-11-23):** not needed, and not claimed in the manuscript.

## Q8. Normalisation of s in (22)/(27) relative to the re-derived form

- Mark's s (and r′) equal ours divided by the unit u, where u² = w = AB′C′/(A′BC). This gives the same mirrors, and changes neither k (taken modulo unit squares) nor the lattice stage.
- N = 4/(r′²(G⁻¹)₃₃) equals Mark's (21), N = 4 + 4(CC′+β+A′B′)/(AB−4), in every case over both rings.
- This settles the "μ′² vs 2μ′²" question in favour of μ′², as the step-2 notes said.
- **Status:** resolved.

## Q9. Bugaenko's extension result for L ⊕ ⟨1⟩^k (ROADMAP D1)

- **The claim:** non-reflectivity propagates upwards (if L ⊕ ⟨1⟩^k is not reflective, then neither is L ⊕ ⟨1⟩^{k+1}). This would justify stopping the higher-dimensional series at the first failure.
- **Source:** attributed to Bugaenko, with the user's note that Mark references it.
- **What we have:** the arXiv text of Mark (1512.01133) cites Bugaenko [6], [7] and [8] (1984, 1990, 1992) only for the modification of Vinberg's algorithm.
- **To do:** find the precise statement (hypotheses and direction) and its exact location before it is used. Not to be assumed.
- **Pointer from the user (2026-11-13):** Bugaenko, *On reflective unimodular hyperbolic quadratic forms*, Selecta Math. Soviet. 9 (1990), Theorem 2. The statement still has to be read from the paper (not available here). The PDF is needed.
- **Located (2026-11-13, user pointer):** Mcleod's thesis (2013), Theorem 3.0.8 (`papers/mcleod_thesis_2013.txt`, lines 1453–1460), restates Bugaenko 1990, Theorem 2.
  - **Statement:** if a hyperbolic form f splits as f′ ⊕ (a one-dimensional unimodular form), then the fundamental polytope P′ of the maximal reflection subgroup of O(f′) is a face of the fundamental polytope P for f.
  - **Consequence:** f reflective (P of finite volume) ⇒ the face P′ has finite volume ⇒ f′ reflective. Contrapositively, L_k not reflective ⇒ L_{k+1} = L_k ⊕ ⟨1⟩ not reflective. No diagonality of f′ is required.
- **Update (2026-11-20, pre-review report):** the paper now cites Bugaenko, Adv. Soviet Math. 8 (1992), Thm 2.1, via Bogachev arXiv:1610.06148, Thm 5.2 / Cor 5.2.1: for L = L′ ⊕ M with M positive definite, the chamber of W(L) meets Λ′ = hyperbolic space of L′ in ∅ or a chamber of W(L′). With M = ⟨1⟩ = ⟨e⟩ and the chamber chosen with a wall on e^⊥, this gives Corollary 14.2 (L_{k+1} reflective ⇒ L_k reflective). Listed as imported in the manuscript; still not read in the original.
- **Status:** statement located through a secondary source (Mcleod's restatement). Still to do: check it against Bugaenko's original when the paper is available, including the ground ring (Mcleod uses it over Q(√5)). Deferred with D1.
- **Update 2026-11-23 (pre-arXiv review):** the paper now cites Bugaenko 1990, Thm 2 (the rank-one unimodular case used) and 1992, Thm 2.1, through the restatements of Bogachev and the author's thesis, lists the theorem as imported, and says that only Corollary 14.2 (monotonicity in k) depends on it; the lower bounds k_A do not. The originals are still unread.

## Q10. Two undetermined ℚ(√13) candidates (2026-11-15)

Neither of these was decided after 12 h of hop search plus walking (`logs/cand_13_pass4.log`):
- the short-pair `[[1,0],[2,1],[0,0],[0,0],[1,0],[31,22],[2,0]]`;
- the short-edge `[[1,0],[1,0],[0,0],[0,0],[1,0],[23,17]]`.

The ℚ(√13) classification (39 classes) is therefore provisional: each candidate could be reflective and add a class.

Next steps:
- test whether either is isometric to an already decided lattice;
- otherwise try a different decision method (a certificate of non-reflectivity from a loxodromic in the stabiliser, or a longer Vinberg run with a different start vector).

Do not assume either way.

**Status (2026-11-23):** still open. The manuscript states the ℚ(√13) result as provisional (at least 39 classes, 2 candidates undecided).
