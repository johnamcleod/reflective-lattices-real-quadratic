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

Also as a provable statement: no reflective SSF rank-3 lattice over ℤ[√2] lies outside these 146 classes. This rests on the completeness of the configuration stage (A.3.2), of the lattice stage (A.3.3, a provable superset), and on local simplicity. The non-merges are now proved without any search: all 146 classes have pairwise different chamber invariants (see *Class counts are exact* below).

**How the candidates were decided (four passes; the method changed, the certificate did not):**

1. Hop search, 40 hops, 15 min limit: 1277 reflective, 603 non-reflective, 493 unresolved.
2. Same with 150 hops and 30 min, after replacing the single-ball polygon check (which needed hours on long polygons) by the ball cover: +3 reflective, +312 non-reflective.
3. Boundary walk (`zphi/walk.py`), passes 3–5. It follows the chamber's boundary corner to corner, each next corner found exactly by covering the wall's ray with small balls. Some walls are extremely long, because crossings repeat with the period of a Pell-type unit of the wall's binary lattice. So the walk uses exact high-precision ray parameters and adaptive-precision bounds. This decided the remaining 178, all non-reflective.

Mark's 522 appendix entries: re-checked with the final `check_polygon` (`tools/verify_mark.py`): **522 / 522 pass**.

**Runtime:** about 12 h for pass 1 on 8 cores; about 8 h for passes 2–5 combined.

### Regression after the field-profile refactor (2026-11-13)

Re-run with the refactored code (commit 84f2248): `verify_all.py` 2373/2373 certificates
pass (1280 reflective, 1093 non-reflective); `verify_mark.py` 522/522; `cand_classes.py`
146 classes, 0 of Mark's classes missing, the same 2 new classes (DISCREPANCIES #5).
Logs: `logs/regr_*.log`.

## ℤ[φ]: configurations, short-edge and short-pair lattice stage, triangles

There are no published values to compare with. The (27) count was cross-checked
configuration by configuration against Mark's matrix (27), as over ℤ[√2]:
`integral = ultraparallel`, 0 mismatches (`logs/close_count_5.log`, 147 slices, about 8 min).

| Type | (15) | (16) | (22) | (23) | (27) |
|---|---|---|---|---|---|
| configurations | 298 | 1636 | 2946 | 36961 | 23700 |
| reflection-stable enlargements | 1629 | 7023 | 3020 | 30934 | 11459 |
| SSF | 168 | 430 | 256 | 1253 | 638 |
| SSF and locally simple (candidates) | 117 | 373 | 204 | 1172 | 564 |

Total: 2430 candidates to decide. Runtime with 8 workers: short edge 178 s, short pair 53 s,
close pair 24 s (plus about 8 min for key generation). Logs: `logs/lat_5_*.log`.

**Triangles.** `zphi/triangles.py` applies Vinberg's arithmeticity criterion exactly:
- the Vinberg field must be generated by γ(m) and 8∏cos(π/mᵢ);
- the conjugate Gram determinant must be positive.

It reproduces the twelve arithmetic triangles with Vinberg field ℚ(√5) and the three
non-arithmetic ones, exactly as in TASK.md (`tests/test_triangles.py`). Over ℚ(√2) it gives 9.
Takeuchi's paper could not be fetched (OPEN_QUESTIONS Q5).


## ℤ[φ]: every candidate decided; 144 classes; gates A.3.5 and A.3.6 passed

**Reflectivity** (`tools/run_candidates.py 5`, then the boundary walk on whatever was left):

| Type | Candidates | Reflective | Non-reflective | Undetermined |
|---|---|---|---|---|
| short edge (15)+(16) | 490 | 221 | 269 | 0 |
| short pair (22)+(23) | 1376 | 518 | 858 | 0 |
| close pair (27) | 564 | 401 | 163 | 0 |
| **total** | **2430** | **1140** | **1290** | **0** |

- Pass 1 (hop search, 15-min limit) left 247 undetermined: 52 short edge, 185 short pair, 10 close pair. The boundary walk decided all 247, all non-reflective (31 min).
- `tools/verify_all.py 5`: every certificate re-checked with the final checkers, 2430/2430 pass (`data/cand_final_5.json`).

**Isometry classes** (`tools/cand_classes.py 5`): the 1140 reflective candidates form **144 classes**. Each merge has an explicit, verified φ. The count equals Mark's ℤ[√2] figure by coincidence.

| Sides | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 16 | 18 | 24 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| classes | 4 | 19 | 15 | 24 | 6 | 24 | 2 | 16 | 1 | 14 | 1 | 7 | 4 | 6 | 1 |

**Gate A.3.5: calibration lattices, passed** (`tools/calibration.py`, `data/calibration_5.json`). Each is reflective with a certified chamber and matched to one of our classes by an explicit isometry:

| Lattice | Chamber angles (m) |
|---|---|
| ⟨−φ,1,1⟩ | (4,2,5) |
| ⟨−√5,1,1⟩ | (4,2,10) |
| ⟨−(3+2√5),1,1⟩ | (4,2,2,3) |
| ⟨−(−3+2√5),1,1⟩ | (4,2,2,3) |
| ⟨−φ,2+φ,1⟩ | (2,2,3,2) |

**Gate A.3.6: diagonal check, passed** (`tools/diagonal_check.py 400`, `data/diagonal_5.json`).
- **(a)** All 38 classes with a π/4 corner are isometric to ⟨−d,1,1⟩, d = −det, by an explicit φ. This confirms the B₂ theorem on the data.
- **(b)** All 149 SSF admissible ⟨−d,1,1⟩ with |N(d)| ≤ 400 were run: 38 reflective, all in our list, and 111 certified non-reflective. The largest |N(d)| among our π/4 classes is 341.

**Triangles** (`tools/triangle_lattices.py`, `data/triangles_5.json`). All twelve arithmetic triangles are realised by SSF lattices, 25 in all:
- (2,3,10), (2,4,5), (2,4,10) and (2,5,6) are chambers (4 classes);
- the other eight sit inside them as reflection subgroups: (2,5,5) ⊂ (2,4,5); (3,3,5), (5,5,5), (2,5,10) ⊂ (2,3,10); (2,10,10), (4,4,5), (5,10,10) ⊂ (2,4,10); (3,5,5) ⊂ (2,5,6).

The commensurability grouping differs from the step-1 notes (DISCREPANCIES #6).

**Outputs:** `data/zphi_rank3.json` and `data/zsqrt2_rank3.json` (`tools/export.py`). They contain every candidate with its Gram matrix, determinant, status and certificate (cyclic simple roots, or translation data), and every class with its polygon and member isometries. The certificates are stored inside these files rather than in a separate `certificates/` directory.

**Runtime, ℤ[φ], 8 cores:**
- configurations 8 min; lattice stage 4 min;
- reflectivity pass 1: 67 min (short edge and short pair) + 15 min (close pair);
- walk pass 31 min; re-verification 40 min; classification about 1 min.

## Wrap-up checks (2026-11-13)

### Class counts are exact (`tools/nonisometry.py`, `data/nonisometry_{5,2}.json`)
The chamber invariant (determinant ideal; cyclic sequence of (root-norm ideal, angle) up to dihedral symmetry) is an isometry invariant. The proof uses only the transitivity of W(L) on chambers (`vinberg_chamber`); it is paper Lemma *chamber invariant*, §12.
- **ℤ[φ]:** the 144 representatives have **144 different invariants**.
- **ℤ[√2]:** the 146 representatives have **146 different invariants**.

So no two classes are isometric, and no alignment search is needed. Together with the explicit merge isometries, **144 and 146 are exact**, not upper bounds. Scaling identifies nothing further, since a rescaling of an SSF lattice that is again SSF is by a totally positive unit, which is a square (U2).

### Independent cross-check with AlVin and CoxIter (`tools/alvin_crosscheck.py`, `data/alvin_crosscheck_5.json`)
AlVin and CoxIter are built at pinned commits by `tools/build_alvin.sh`. AlVin was run over Q[√5] on all 149 SSF admissible ⟨−d,1,1⟩ with |N(d)| ≤ 400. AlVin's `T(5)` is φ.

| our status | cases | AlVin agrees | notes |
|---|---|---|---|
| non-reflective (certified) | 111 | 111 | AlVin never terminates; no contradiction |
| reflective | 38 | 29 fully | AlVin terminates, root sets equal up to units, CoxIter: cocompact, finite covolume |
| reflective | | 9 partly | AlVin had not terminated after 30 min; every root it had printed (10–17) is a root of our certified chamber (12–18 sides) |

**No contradiction.** The 9 partial cases have 12–18 sides. AlVin's termination test is slow on long polygons. Our decisions there rest on our certificates.

Two technical points:
- AlVin is run under a pseudo-terminal, so that its line-buffered output survives a timeout. With a pipe, the roots printed before the kill were lost.
- Run directly, AlVin keeps printing roots of our chamber.

### Triangle data in the outputs
`data/zphi_rank3.json` classes now carry `triangle_type` (triangular chambers) and `triangle_subgroups` (the arithmetic triangle groups contained in W(L), from `data/triangles_5.json`). The four triangle chambers contain, respectively:
- (2,3,10) ⊃ (2,5,10), (3,3,5), (5,5,5);
- (2,4,5) ⊃ (2,5,5);
- (2,4,10) ⊃ (2,10,10), (4,4,5), (5,10,10);
- (2,5,6) ⊃ (3,5,5).

## ℚ(√13): first results (2026-11-14, provisional until the last 2 candidates are decided)

Ring ℤ[ω], where ω = (1+√13)/2 and ω² = 3 + ω. The fundamental unit is ε = 1 + ω, of norm −1, so (N2) holds. The ring is norm-Euclidean (rounding bound 13/16). The prime 2 is inert, 3 splits, and 13 ramifies. Admissible angles are π/m with m ∈ {2, 3, 4, 6}.

**Lattice stage** (locally simple SSF candidates per configuration type):

| type | configurations | SSF | locally simple |
|---|---|---|---|
| (15) | 78 | 28 | 26 |
| (16) | 743 | 122 | 112 |
| (22) | 1792 | 72 | 55 |
| (23) | 37671 | 458 | 433 |
| (27) | 20071 | 216 | 185 |

Total: 811 candidates. The close-pair recount `count_close` gives 20071 configurations with 0 mismatches.

**Reflectivity** (every decided status re-verified by `verify_all.py`):

| pass | reflective | non-reflective | undetermined |
|---|---|---|---|
| hop search | 364 | 355 | 92 |
| + walk, 900 s limit | 365 | 443 | 3 |
| + walk, 2 h limit | 365 | 444 | 2 |
| + walk, 12 h limit | running | | |

**Classes.** 39 isometry classes of reflective lattices, with pairwise distinct chamber invariants. So 39 is exact, apart from the 2 undetermined candidates, which could add classes. By number of sides:

| sides | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 | 14 | 16 | 18 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| classes | 8 | 2 | 6 | 1 | 7 | 1 | 4 | 4 | 4 | 1 | 1 |

There are **no triangles**. This is yet to be compared with Takeuchi's list of arithmetic triangle groups.

**Diagonal check** (analogue of gate A.3.6; Theorem B₂ applies because 2 is inert):
- (a) All 13 classes with a π/4 corner are isometric to a diagonal ⟨−d,1,1⟩, each by an explicit isometry.
- (b) Of the 198 values of d with |N(d)| ≤ 400, 13 give a reflective ⟨−d,1,1⟩ and 185 are certified non-reflective. No reflective one is missing from (a).

**AlVin cross-check** (all 198 diagonal forms):
- 195 agree completely.
- 2 are partial: AlVin did not finish in 30 min, but all the roots it printed lie in our chamber.
- 1 is an AlVin error: for ⟨−ω,1,1⟩ AlVin misses the root (ω−1, ω, 0) and returns an index-3 pentagon. See DISCREPANCIES #7.
