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

## ℤ[φ] configuration counts so far (regression only; no published values)

| Type | (15) | (16) | (22) | (23) | (27) |
|---|---|---|---|---|---|
| ℤ[φ] | 298 | 1636 | 2946 | 36961 | not yet run (a configuration count of about 10 min; the lattice stage comes later) |
