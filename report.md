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

## ℤ[φ] configuration counts so far (regression only; no published values)

| Type | (15) | (16) | (22) | (23) | (27) |
|---|---|---|---|---|---|
| ℤ[φ] | 298 | 1636 | 2946 | 36961 | not yet run (a configuration count of about 10 min; the lattice stage comes later) |
