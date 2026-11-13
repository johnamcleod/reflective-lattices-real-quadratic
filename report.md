# Report

This file is updated at each gate. All timings are on this machine (Apple silicon, 8 cores, 16 GB), Python 3.10 with exact integer arithmetic.

## Gate A.3.1: unit tests (passed)

`pytest -m gate1` covers the following:

| Area | Checks |
|---|---|
| Ring arithmetic over ℤ, ℤ[√2], ℤ[φ] | agrees with the prototype on 400 random pairs per ring; exact signs agree with float signs on 2000 samples |
| Units | (U2) checked for ±ε^k with |k| ≤ 12; `unit_sqrt` |
| Residue fields (step-1 §1) | φ has order 3 mod 2, 8 mod 3, 4 mod π |
| Prime decomposition | 2 and 3 inert and 5 = (π)² in ℤ[φ]; 2 = (√2)², with 3 and 5 inert, in ℤ[√2] |
| Factorisation and divisors | factorisation agrees with PARI `idealfactor`; divisors agree with brute force; the number of ideal divisors is ∏(eᵢ+1) |
| SNF | U·A·V = S, the divisibility chain, U and V unimodular (60 random matrices per ring); the elementary divisors equal PARI `nfsnf` |
| Local superlattices | containment, no duplicates, and the count equals Birkhoff's formula for submodules of ⊕O/𝔭^{eᵢ}; the formula itself is checked against brute-force subgroup enumeration |
| Boxes (step-1 §5) | 7/57/350/807/1603 elements and 11/147/1126/2902/6217 factorisation classes; the first box is {φ⁻², 1, π, 2, φ², 3, ρ}; boxes agree with brute force |
| Corner hulls (step-1 §4 table) | A₂ → O/3, B₂ → O/2, G₂ → 0, H₂ → O/π, I₂(10) → 0; det I₂(10) = ρ(4−ρ) = π |
| Mirror-line counts (`corner_check.py`, re-derived) | unglued A₂ → 6, glued → 3; unglued H → 10, glued H₂ → 5 |
| Oracle | the candidate lattices agree with the prototype as sublattices of K³ on 40 random short-edge configurations per ring |

## Gate A.3.2: ℤ[√2] configuration counts (passed)

| Mark's type | Lemma | Ours | Mark Table 1 | Mark's printed matrix = ours | Time |
|---|---|---|---|---|---|
| (15) | 9, A′B′ > 0 | **282** | 282 | all 282 | 2 s (both types) |
| (16) | 9, T ⊥ R′ | **1736** | 1736 | all 1736 | |
| (22) | 10, A′B′ > 0 | **5777** | 5777 | all 5777 (after the unit rescaling s, r′ ↦ ·/u) | about 2 min (both types) |
| (23) | 10, T ⊥ R′ | **88836** | 88836 | all 88836 | |
| (27) | 11 | **97526** | 97526 | all 97526, including γ from (26) | 76 CPU-min, about 10 min wall on 8 workers |

Notes:

- The printed full vertex box gives 360/1794 instead of 282/1736. Mark's program used AB ∈ {4cos²(π/m)} (DISCREPANCIES #1).
- The ultraparallel filter on (S, S′) removes no close-pair configuration (OPEN_QUESTIONS Q1).
- The prototype needed more than 40 minutes and never finished the close pairs; Mark reports about 10 days.

## Gate A.3.3: ℤ[√2] lattice stage (explained, not reproduced item by item)

For each configuration we list every lattice M with ⟨roots⟩ ⊆ M ⊆ H (the reflective hull of the configuration roots) in which every configuration root is primitive ("enlargements"). We then mark the SSF ones, and among those the ones passing Mark's local-simplicity condition §2.8(3): at each configuration vertex of angle π/m there are exactly m mirrors of M.

| Type | Configs | Enlargements: ours / Mark | SSF: ours / Mark | SSF + locally simple (ours) |
|---|---|---|---|---|
| (15) | 282 | 1998 / 1489 | 134 / 130 | 77 |
| (16) | 1736 | 9351 / 7181 | 351 / 341 | 286 |
| (22) | 5777 | 5055 / 3653 | 247 / 233 | 176 |
| (23) | 88836 | 61150 / 38871 | 1262 / 1096 | 1190 |
| (27) | 97526 | 24706 / 13688 | 704 / 581 | 644 |
| **Total** | 194157 | 102260 / 64882 | 2698 / 2381 | 2373 |

How to read this:

- Our counts are larger than Mark's for every type. Our enlargement set is, by construction, every lattice in which the configuration vectors are roots, so it is a superset of what is needed and the classification stays complete.
- Mark's smaller numbers come from a different hull (§2.9 uses all roots of R) and from her unremoved redundancies. Her §3.5 says the numbers are "large overestimates". Re-implementing her all-roots hull for type (15) gives 1266/129, 1093/128 and 996/124 as the root search box grows. None of these is her 1489/130, and the method can drop lattices, since a root of R need not stay a root of M.
- The comparison that matters is the final reflective list (gate A.3.4: ours vs her 432). See DISCREPANCIES #3 and OPEN_QUESTIONS Q3.

Runtime (8 workers):

- short edges: a few minutes;
- short pairs: about 15 min;
- close pairs: about 7 h wall. Almost all of it was spent on 5 configurations whose local-simplicity Fincke–Pohst ran on an unreduced basis.
  - **Fix:** exact LLL on the trace form before enumeration (`definite.lll_gram`, `short_vectors_reduced`). The vector sets are unchanged (tested).
  - The 5 configurations then took 0.5 s each, so a rerun of the whole stage would be well under an hour.

## Gate A.3.4 (part 1): Mark's appendix, verified and classified

`tools/check_mark.py` and `tools/mark_classes.py` produce `data/mark_check.json` and `data/mark_classes.json`.

| | Count |
|---|---|
| Entries parsed from the appendix | 522 |
| Certified reflective: exact polygon certificate on the full chamber | **522** |
| Chamber equals Mark's printed simple roots (for symmetric entries, the printed period and its images) | **522** |
| Isometry classes | **144** (Mark: 432) |
| Merge certificates φ ∈ GL₃(ℤ[√2]), φᵀ G_rep φ = G_entry, re-verified in PARI | 378 / 378 |

How each chamber was found:

- 384 entries ran Vinberg from an interior point built from the printed roots.
- 105 entries used hop search. Vinberg runs to a small radius; the control point then hops to a point that is provably inside the same chamber, and this repeats until the walls close.
- 33 entries ran Vinberg from a vertex, because their printed period is too short to give an interior point.

In every case the chamber found was then checked by the exact polygon certificate, which is the proof of reflectivity.

The 432 vs 144 gap is DISCREPANCIES #4 and is still open.

## Gate A.3.4 (part 2): every candidate decided; 146 classes

Tools: `tools/run_candidates.py` (passes), `tools/verify_all.py` → `data/cand_final_2.json`, `tools/cand_classes.py` → `data/cand_classes_2.json`.

Every one of the 2373 SSF, locally simple candidates (gate A.3.3) is decided by an exact certificate:

| Type | Reflective | Non-reflective | Undetermined |
|---|---|---|---|
| short edge (15) | 179 | 184 | 0 |
| short pair (16)/(22)/(23) | 622 | 744 | 0 |
| close pair (27) | 479 | 165 | 0 |
| **Total** | **1280** | **1093** | **0** |

- **Reflective:** a polygon certificate (Prop. *polygon certificate*, §7). It checks the Coxeter angles and that the vertices are strictly inside and in one sheet. It also enumerates every mirror within a cover of the polygon by small balls (balls are convex).
- **Non-reflective:** a translation certificate (Prop. *translation certificate*, §7). Two corners of the chamber are certified with their mirror counts. The segments from an interior point to both corners are certified mirror-free. Finally, g ∈ GL₃(ℤ[√2]) is an isometry mapping one corner onto the other, with tr g > 3 (so infinite order).
- **Final re-check:** all 2373 certificates were re-verified with the final code (`verify_all.py`): **1280 + 1093 / 2373 pass**.

**Isometry classes.** The 1280 reflective lattices were classified together with one representative of each of Mark's 144 classes. Each merge has an explicit φ with φᵀG_rep φ = G (1278 φ's, each re-verified). The outcome:
- **146 classes.** All 144 of Mark's classes occur, each matched to our lattices by explicit isometries.
- **2 classes do not occur in Mark's appendix** (DISCREPANCIES #5). They differ from every entry in an isometry invariant: the determinant ideal, and the cyclic sequence of (root norm mod unit squares, angle).
  - **A:** quadrilateral π/8, π/2, π/8, π/2, det 4−5√2.
  - **B:** hexagon π/4, π/2, π/8 (×2), det −9−7√2.

  Each is the "other prime above 17" twin of a Mark entry (lines 2840 and 5476).

Also as a provable statement: no reflective SSF rank-3 lattice over ℤ[√2] lies outside these 146 classes. This rests on the completeness of the configuration stage (A.3.2), of the lattice stage (A.3.3, a provable superset), and on local simplicity. It also assumes the chamber-alignment isometry search is complete (non-merges); compare DISCREPANCIES #4.

**How the candidates were decided (four passes; the method changed, the certificate did not):**

1. Hop search, 40 hops, 15 min limit: 1277 reflective, 603 non-reflective, 493 unresolved.
2. Same with 150 hops and 30 min, after replacing the single-ball polygon check (which needed hours on long polygons) by the ball cover: +3 reflective, +312 non-reflective.
3. Boundary walk (`zphi/walk.py`), passes 3–5. It follows the chamber's boundary corner to corner, each next corner found exactly by covering the wall's ray with small balls. Some walls are extremely long, because crossings repeat with the period of a Pell-type unit of the wall's binary lattice. So the walk uses exact high-precision ray parameters and adaptive-precision bounds. This decided the remaining 178, all non-reflective.

Mark's 522 appendix entries: re-checked with the final `check_polygon` (`tools/verify_mark.py`): **522 / 522 pass**.

**Runtime:** about 12 h for pass 1 on 8 cores; about 8 h for passes 2–5 combined.

## ℤ[φ] configuration counts so far (regression only; no published values)

| Type | (15) | (16) | (22) | (23) | (27) |
|---|---|---|---|---|---|
| ℤ[φ] | 298 | 1636 | 2946 | 36961 | not yet run (a configuration count of about 10 min; the lattice stage comes later) |
