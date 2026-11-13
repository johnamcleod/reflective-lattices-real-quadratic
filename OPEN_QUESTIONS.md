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
  - **2026-11-13, ℤ[φ] pass 1, short edge:** of the twelve arithmetic triangles, only (2,3,10), (2,4,5), (2,4,10) and (2,5,6) occur as the chamber of a reflective SSF candidate.
    - The other eight may be finite-index subgroups of these four, for example (2,5,5) and (4,4,5) in (2,4,5). A lattice realising one of them would then have a strictly larger reflection group.
    - 52 short-edge candidates are still undetermined after pass 1.
    - Still to settle:
      - (a) for each of the eight, exhibit a lattice realising it and identify its full reflection group;
      - (b) decide how TASK.md's calibration item "lattices realising the twelve triangles" is to be read: as lattices whose reflection group is the triangle group, or as lattices whose group contains it.
- **Guglielmetti's ⟨−√5,1,1⟩ and ⟨−φ,2+φ,1⟩:** fetch the thesis.
- **Bugaenko's ⟨−φ,1,1⟩:** primary source probably unavailable; also check by computation.
- **Mcleod thesis §3.2:** a copy is in the sibling project.

## Q6. The H₂ glue-sign lemma (the analogue of Mark's Lemmas 6–7)

- This must be proved before walking can use H₂ glue signs. Until then, walking uses A₂ signs only, and Vinberg is used everywhere else.

## Q7. Step-1 §4.1 for A₁² corners

- The claim that "b is a unit" is unproven for right-angled corners (step-1 §9 item 4). Not needed by the pipeline, which handles A₁² generically, but the manuscript must not claim it.

## Q8. Normalisation of s in (22)/(27) relative to the re-derived form

- Mark's s (and r′) equal ours divided by the unit u, where u² = w = AB′C′/(A′BC). This gives the same mirrors, and changes neither k (taken modulo unit squares) nor the lattice stage.
- N = 4/(r′²(G⁻¹)₃₃) equals Mark's (21), N = 4 + 4(CC′+β+A′B′)/(AB−4), in every case over both rings.
- This settles the "μ′² vs 2μ′²" question in favour of μ′², as the step-2 notes said.
- **Status:** resolved.
