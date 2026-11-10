# Open questions

Each entry gives its status and how it will be resolved. None of these is assumed away.

## Q1. The close-pair conditions: Mark's γ-test versus the prototype

- **Mark** (Lemma 11, (25)–(26)) requires γk²/(A′BN) ∈ o and γk′²/(AB′N′) ∈ o, with γ given in closed form.
- **The prototype** (`rank3.enumerate_close_pair`) computes s and s′ explicitly. It requires 2(s·s′)/s² ∈ O and 2(s·s′)/s′² ∈ O, and in addition s·s′ < 0 and (s·s′)² > s²s′² (S and S′ ultraparallel).
- **Why it matters.** The two must be shown equivalent, up to the extra geometric filters. Mark may or may not have imposed the ultraparallel filter, which would change the count of 97526. The ℤ[√2] close-pair count was never finished in the prototype.
- **Status:** open. Resolve by comparing both implementations over ℤ[√2] (gate A.3.2).

## Q2. The Coxeter restriction in Lemma 9

- Mark's Lemma 9 is printed with the full box 0 < AB, A′B′ < 4. The counts 282/1736 are reproduced only with AB, A′B′ ∈ {4cos²(π/m)}; the full box gives 360/1794.
- **Status:** the counts suggest Mark's program imposed the restriction. It is geometrically valid, because R∩T is a vertex of a Coxeter polygon. It is also needed for CC′ < 4. To be stated explicitly in the manuscript.

## Q3. Short-edge lattices: 134/351 versus Mark's 130/341

- Mark §3.5 also "removed any where the root sequence was not a chain of roots due to not being locally simple". The prototype does not.
- **Status:** hypothesis, to be tested in gate A.3.3 by adding a local-simplicity filter. A second possible cause is the hull: Mark used all roots of R, the prototype only the configuration roots, which would make the prototype's list larger.

## Q4. Missing companion files

- `qsqrt5.py`, `step1_compute.py`, `corner_check.py` and `step1_results.json` were not supplied.
- **User decision:** re-derive their checks as tests, using the numbers in `notes/step1-zphi-lemmas.md` as expected values.

## Q5. Secondhand data to verify against sources

- **Takeuchi's ℚ(√5) triangles and their commensurability classes:** fetch J. Math. Soc. Japan 29 (1977), and also Takeuchi, J. Fac. Sci. Univ. Tokyo 24 (1977) for the commensurability classes.
- **Guglielmetti's ⟨−√5,1,1⟩ and ⟨−φ,2+φ,1⟩:** fetch the thesis.
- **Bugaenko's ⟨−φ,1,1⟩:** primary source probably unavailable; also check by computation.
- **Mcleod thesis §3.2:** a copy is in the sibling project.

## Q6. The H₂ glue-sign lemma (the analogue of Mark's Lemmas 6–7)

- This must be proved before walking can use H₂ glue signs. Until then, walking uses A₂ signs only, and Vinberg is used everywhere else.

## Q7. Step-1 §4.1 for A₁² corners

- The claim that "b is a unit" is unproven for right-angled corners (step-1 §9 item 4). Not needed by the pipeline, which handles A₁² generically, but the manuscript must not claim it.
