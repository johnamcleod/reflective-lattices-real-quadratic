# Rank 3 reflective hyperbolic lattices over real quadratic fields

Code and data for the manuscript *Rank 3 reflective hyperbolic lattices over real quadratic fields*.

The project classifies the strongly squarefree (SSF) reflective hyperbolic lattices of rank 3 over the rings of integers of ℚ(√2), ℚ(√5) and ℚ(√13). It uses a field-independent version of Mark's method:

1. The thin part of a chamber (Allcock) gives a short list of root configurations.
2. Each configuration gives finitely many candidate lattices.
3. Each candidate is decided by an exact certificate: a Coxeter polygon if it is reflective, or a loxodromic symmetry if it is not.

The results are:

- **ℤ[√2]:** reproduces Mark's list (144 isometry classes) and finds 2 more classes.
- **ℤ[φ]:** 144 classes. The Lean 4 kernel has checked the reflectivity certificates of all 144 classes and the isometries within each class.
- **ℚ(√13):** 39 classes; 2 candidates are undecided, so there are at most 41.
- **Higher dimensions:** for the diagonal classes ⟨−d,1,1⟩, lower bounds for the largest k such that L ⊕ ⟨1⟩ᵏ is reflective.

All computation is in exact arithmetic. Lean is used kernel-only: no `native_decide` and no `sorry`. Imported results enter Lean as explicit hypotheses, not axioms.

## Layout

| Path | Contents |
|---|---|
| [`zphi/`](zphi/) | Python library: exact arithmetic, configurations, candidate lattices, Vinberg's algorithm, certificates |
| [`tools/`](tools/) | Pipeline drivers, cross-checks, certificate emitters, generators for the paper's tables and diagrams |
| [`lean/`](lean/) | Lean 4 + Mathlib development (`ReflectZphi`) and the emitted certificates |
| [`data/`](data/) | Results: candidates, classes, certificates, isometries, higher-dimensional chambers |
| [`logs/`](logs/) | The run logs cited as evidence (the rest of the logs are not kept) |
| [`tests/`](tests/) | pytest suite: unit tests, oracle tests against the prototype, validation gates |
| [`prototype/`](prototype/) | The original Python prototype, kept unchanged as a test oracle |
| [`notes/`](notes/) | The step-1 and step-2 notes the computation started from |
| [`methods.md`](methods.md), [`lean-plan.md`](lean-plan.md) | Conventions, pipeline and the design of the Lean development |
| [`report.md`](report.md) | Run report, gate by gate |
| [`DISCREPANCIES.md`](DISCREPANCIES.md), [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md) | Every disagreement with the literature, and every unresolved doubt |

## Where the paper refers to the code

Section numbers are those of the current manuscript.

### Part 1: the general method

- **§1 Introduction.** The field enters only as a *profile* (c₀, c₁): [`zphi/fields.py`](zphi/fields.py).
- **§2 Preliminaries.**
  - The implementation checks the hypotheses (H1), (H2) and (N2) before any computation: [`zphi/fields.py#L113`](zphi/fields.py#L113).
  - Exact arithmetic in O: [`zphi/ring.py`](zphi/ring.py) and [`zphi/linalg.py`](zphi/linalg.py).
  - Lean: `zphi_isPID` in [`Ring/ZPhi.lean#L34`](lean/ReflectZphi/Ring/ZPhi.lean#L34).
- **§3 Root norms.**
  - Candidate root norms are the divisors of 2·det (Lemma 3.2), as used in [`zphi/vinberg.py`](zphi/vinberg.py) and [`zphi/vinbergn.py`](zphi/vinbergn.py).
  - Lean: `root_norm_dvd` in [`Cert/RootNorms.lean#L105`](lean/ReflectZphi/Cert/RootNorms.lean#L105).
- **§4 Angles.** The exact Chebyshev test for γ(m), and the choice of the conjugate: [`zphi/boxes.py#L72`](zphi/boxes.py#L72) and [`zphi/fields.py`](zphi/fields.py).
- **§5 Configurations.**
  - Short edges, short pairs and close pairs (Mark's Lemmas 9–11): [`zphi/configs.py`](zphi/configs.py).
  - Boxes and good factorisations (§5.3): [`zphi/boxes.py`](zphi/boxes.py).
  - Parallel close-pair count: [`zphi/count_close.py`](zphi/count_close.py).
- **§6 Candidates.**
  - From a configuration to candidate SSF lattices (hull, SNF, local choices, CRT): [`zphi/lattices.py`](zphi/lattices.py).
  - The local-simplicity filter: [`zphi/lattices.py#L351`](zphi/lattices.py#L351).
  - Driver: [`zphi/run_lattices.py`](zphi/run_lattices.py).
- **§7 Reflectivity.**
  - Rank-3 Vinberg algorithm and the exact polygon certificate: [`zphi/vinberg.py`](zphi/vinberg.py) (`check_polygon`, [L520](zphi/vinberg.py#L520)).
  - Chamber search: [`zphi/chamber.py`](zphi/chamber.py).
  - Boundary walk (§7.4): [`zphi/walk.py`](zphi/walk.py).
  - Non-reflectivity certificates: [`zphi/nonrefl.py`](zphi/nonrefl.py) (`check_nonreflective`, [L71](zphi/nonrefl.py#L71)).
  - Short vectors in definite sublattices: [`zphi/definite.py`](zphi/definite.py).
  - Driver over all candidates: [`tools/run_candidates.py`](tools/run_candidates.py).
  - Re-verification of all certificates: [`tools/verify_all.py`](tools/verify_all.py).

### Part 2: the three fields

- **§8 ℤ[√2].**
  - Mark's appendix, parsed and checked: [`tools/parse_mark_appendix.py`](tools/parse_mark_appendix.py), [`tools/check_mark.py`](tools/check_mark.py) and [`tools/verify_mark.py`](tools/verify_mark.py).
  - Isometry classes of her 522 entries: [`tools/mark_classes.py`](tools/mark_classes.py), giving [`data/mark_classes.json`](data/mark_classes.json).
  - The two new classes: [`data/zsqrt2_rank3.json`](data/zsqrt2_rank3.json).
  - Lean: `zsqrt2_isPID` and `norm_epsSqrt2` in [`Ring/ZSqrt2.lean`](lean/ReflectZphi/Ring/ZSqrt2.lean#L31).
- **§9 ℤ[φ] arithmetic.** Lean, in [`Ring/ZPhi.lean`](lean/ReflectZphi/Ring/ZPhi.lean), [`Ring/Euclid.lean`](lean/ReflectZphi/Ring/Euclid.lean) and [`Ring/Embed.lean`](lean/ReflectZphi/Ring/Embed.lean):

  | Lean name | Location |
  |---|---|
  | `isPrincipalIdealRing` | [`Euclid.lean#L178`](lean/ReflectZphi/Ring/Euclid.lean#L178) |
  | `norm_phi` | [`ZPhi.lean#L39`](lean/ReflectZphi/Ring/ZPhi.lean#L39) |
  | `isUnit_phi` | [`ZPhi.lean#L41`](lean/ReflectZphi/Ring/ZPhi.lean#L41) |
  | `five_eq` | [`ZPhi.lean#L44`](lean/ReflectZphi/Ring/ZPhi.lean#L44) |
  | `norm_piZ` | [`ZPhi.lean#L46`](lean/ReflectZphi/Ring/ZPhi.lean#L46) |
  | `norm_mod_five` | [`ZPhi.lean#L60`](lean/ReflectZphi/Ring/ZPhi.lean#L60) |
  | `prime_two` | [`ZPhi.lean#L104`](lean/ReflectZphi/Ring/ZPhi.lean#L104) |
  | `prime_three` | [`ZPhi.lean#L110`](lean/ReflectZphi/Ring/ZPhi.lean#L110) |
  | `emb_pos_iff` | [`Embed.lean#L90`](lean/ReflectZphi/Ring/Embed.lean#L90) |
- **§12 ℤ[φ] results.**
  - Final export: [`tools/export.py`](tools/export.py), giving [`data/zphi_rank3.json`](data/zphi_rank3.json).
  - Isometry classes and non-isometry: [`tools/cand_classes.py`](tools/cand_classes.py), [`tools/nonisometry.py`](tools/nonisometry.py) and [`zphi/isometry.py`](zphi/isometry.py).
  - The diagonal classes ⟨−d,1,1⟩: [`tools/diagonal_check.py`](tools/diagonal_check.py).
  - Calibration lattices: [`tools/calibration.py`](tools/calibration.py).
  - Arithmetic triangles (Takeuchi's list recomputed): [`zphi/triangles.py`](zphi/triangles.py) and [`tools/triangle_lattices.py`](tools/triangle_lattices.py).
  - Cross-check with AlVin and CoxIter: [`tools/alvin_crosscheck.py`](tools/alvin_crosscheck.py), giving [`data/alvin_crosscheck_5.json`](data/alvin_crosscheck_5.json).
  - Lean: `VinbergChamber` in [`Imported.lean#L82`](lean/ReflectZphi/Imported.lean#L82).
- **§13 ℚ(√13).**
  - Results: [`data/zsqrt13_rank3.json`](data/zsqrt13_rank3.json).
  - AlVin cross-check: [`data/alvin_crosscheck_13.json`](data/alvin_crosscheck_13.json).
  - Lean, in [`Ring/ZSqrt13.lean`](lean/ReflectZphi/Ring/ZSqrt13.lean) unless noted:

    | Lean name | Location |
    |---|---|
    | `boxBound_three_one` | [`Euclid.lean#L88`](lean/ReflectZphi/Ring/Euclid.lean#L88) |
    | `zsqrt13_isPID` | [`#L36`](lean/ReflectZphi/Ring/ZSqrt13.lean#L36) |
    | `norm_eps13` | [`#L41`](lean/ReflectZphi/Ring/ZSqrt13.lean#L41) |
    | `isUnit_eps13` | [`#L43`](lean/ReflectZphi/Ring/ZSqrt13.lean#L43) |
    | `three_eq` | [`#L47`](lean/ReflectZphi/Ring/ZSqrt13.lean#L47) |
    | `thirteen_eq` | [`#L52`](lean/ReflectZphi/Ring/ZSqrt13.lean#L52) |
    | `prime_two_13` | [`#L91`](lean/ReflectZphi/Ring/ZSqrt13.lean#L91) |

### Part 3: extensions

- **§14 Higher dimensions.**
  - AlVin and CoxIter runs on L_k: [`tools/d1_diagonal.py`](tools/d1_diagonal.py), giving [`data/d1_diag_5.jsonl`](data/d1_diag_5.jsonl) and [`data/d1_diag_13.jsonl`](data/d1_diag_13.jsonl).
  - The *general implementation* of Vinberg's algorithm in any rank: [`zphi/vinbergn.py`](zphi/vinbergn.py). Cross-check driver: [`tools/d1_crosscheck.py`](tools/d1_crosscheck.py).
  - The *diagonal fast path*: [`zphi/vinbergdiag.py`](zphi/vinbergdiag.py). Driver: [`tools/d1_fast.py`](tools/d1_fast.py), giving [`data/d1_fast_5.jsonl`](data/d1_fast_5.jsonl) and [`data/d1_fast_13.jsonl`](data/d1_fast_13.jsonl).
  - Every AlVin root is a genuine root: [`tools/d1_rootcheck.py`](tools/d1_rootcheck.py).
  - Chamber roots: [`tools/d1_roots.py`](tools/d1_roots.py) and [`tools/d1_roots_ours.py`](tools/d1_roots_ours.py).
  - Root tables (§14.5) and Coxeter diagrams (§14.4): [`tools/d1_tables.py`](tools/d1_tables.py) and [`tools/d1_tikz.py`](tools/d1_tikz.py). The graphs are in [`data/d1_graphs_5/`](data/d1_graphs_5/) and [`data/d1_graphs_13/`](data/d1_graphs_13/).
  - The AlVin crash and its fix (Remark in §14): [`tools/patches/port_alvin.py`](tools/patches/port_alvin.py) and [`logs/redo_m15_9.out`](logs/redo_m15_9.out).
  - McLeod's form (Remark 14.3): [`tools/scratch/mcleod_check.py`](tools/scratch/mcleod_check.py).
- **§15 Limitations.** See [`OPEN_QUESTIONS.md`](OPEN_QUESTIONS.md) and [`DISCREPANCIES.md`](DISCREPANCIES.md).

### Appendix

- **A.1 Imported results.** [`lean/ReflectZphi/Imported.lean`](lean/ReflectZphi/Imported.lean): `AllcockThinPart` ([L35](lean/ReflectZphi/Imported.lean#L35)) and `VinbergChamber` ([L82](lean/ReflectZphi/Imported.lean#L82)). The axiom check is [`lean/scripts/check_axioms.sh`](lean/scripts/check_axioms.sh).
- **A.2 Formal verification of the reflectivity certificates.**
  - Emitters: [`tools/emit_cert.py`](tools/emit_cert.py), [`tools/emit_sub.py`](tools/emit_sub.py), [`tools/emit_lean.py`](tools/emit_lean.py) and [`tools/cert_all.py`](tools/cert_all.py).
  - Kernel checks: [`tools/check_certs.py`](tools/check_certs.py) and [`tools/check_split.py`](tools/check_split.py).
  - Status logs: [`logs/check_5.jsonl`](logs/check_5.jsonl), [`logs/check_split_5.jsonl`](logs/check_split_5.jsonl), [`logs/cert_5.jsonl`](logs/cert_5.jsonl) and [`logs/recheck_5.jsonl`](logs/recheck_5.jsonl).
  - Certificates: [`lean/ReflectZphi/Data/Cert5/`](lean/ReflectZphi/Data/Cert5/). Isometries: [`lean/ReflectZphi/Data/`](lean/ReflectZphi/Data/) (`Iso5_*.lean`).
  - Lean names cited in A.2:

    | Lean name | Location |
    |---|---|
    | `Reflective` | [`Lattice/Basic.lean#L103`](lean/ReflectZphi/Lattice/Basic.lean#L103) |
    | `basisCheck` | [`Cert/Check.lean#L137`](lean/ReflectZphi/Cert/Check.lean#L137) |
    | `polyCheck` | [`Cert/Check.lean#L144`](lean/ReflectZphi/Cert/Check.lean#L144) |
    | `admCheck` | [`Cert/Check.lean#L231`](lean/ReflectZphi/Cert/Check.lean#L231) |
    | `posDef_of_orth` | [`Cert/Check.lean#L237`](lean/ReflectZphi/Cert/Check.lean#L237) |
    | `reflective_of_check` | [`Cert/Check.lean#L365`](lean/ReflectZphi/Cert/Check.lean#L365) |
    | `isChamber_of_cert` | [`Cert/Bridge.lean#L246`](lean/ReflectZphi/Cert/Bridge.lean#L246) |
    | `reflective_of_cert` | [`Cert/Bridge.lean#L292`](lean/ReflectZphi/Cert/Bridge.lean#L292) |
    | `exists_root_in_window` | [`Cert/RootNorms.lean#L395`](lean/ReflectZphi/Cert/RootNorms.lean#L395) |
    | `windowNorms_of_chunks` | [`Cert/WinSplit.lean#L61`](lean/ReflectZphi/Cert/WinSplit.lean#L61) |
    | `segment_lat` | [`Cert/Cells.lean#L112`](lean/ReflectZphi/Cert/Cells.lean#L112) |
    | `cell_oneSign` | [`Cert/Cells.lean#L201`](lean/ReflectZphi/Cert/Cells.lean#L201) |
    | `hone_of_cells` | [`Cert/Cells.lean#L283`](lean/ReflectZphi/Cert/Cells.lean#L283) |
    | `subCheck` | [`Cert/Sublat.lean#L76`](lean/ReflectZphi/Cert/Sublat.lean#L76) |
    | `sub_coords` | [`Cert/Sublat.lean#L105`](lean/ReflectZphi/Cert/Sublat.lean#L105) |
    | `sub_oneSign` | [`Cert/Sublat.lean#L174`](lean/ReflectZphi/Cert/Sublat.lean#L174) |
    | `cellOK_of` | [`Cert/Sublat.lean#L300`](lean/ReflectZphi/Cert/Sublat.lean#L300) |
    | `reflective_of_checkM` | [`Cert/Sublat.lean#L380`](lean/ReflectZphi/Cert/Sublat.lean#L380) |
    | `enumS_of_coverL` | [`Cert/Cover.lean#L136`](lean/ReflectZphi/Cert/Cover.lean#L136) |
    | `checkIso` | [`Cert/Iso.lean#L20`](lean/ReflectZphi/Cert/Iso.lean#L20) |
    | `checkIso_sound` | [`Cert/Iso.lean#L23`](lean/ReflectZphi/Cert/Iso.lean#L23) |
- **A.3–A.5 The lists.** Generated by [`tools/appendix_lists.py`](tools/appendix_lists.py) from [`data/zphi_rank3.json`](data/zphi_rank3.json), [`data/zsqrt2_rank3.json`](data/zsqrt2_rank3.json) and [`data/zsqrt13_rank3.json`](data/zsqrt13_rank3.json).
- **A.6 Code and data.**
  - This repository.
  - AlVin and CoxIter are built from the pinned upstream commits in [`tools/AlVin.commit`](tools/AlVin.commit) and [`tools/CoxIter.commit`](tools/CoxIter.commit), by [`tools/build_alvin.sh`](tools/build_alvin.sh), with the port and fix in [`tools/patches/port_alvin.py`](tools/patches/port_alvin.py).

## Running it

```sh
python3.10 -m venv .venv && .venv/bin/pip install -r requirements.txt   # needs PARI/GP 2.17 (libpari) for cypari2
.venv/bin/pytest                                                       # unit, oracle and gate tests
cd lean && lake exe cache get && lake build                            # the Lean library (Lean v4.35.0, Mathlib v4.35.0)
lean/scripts/check_axioms.sh                                           # axiom report for the main theorems
.venv/bin/python tools/check_certs.py 5                                # kernel-check the Z[phi] certificates (long)
tools/build_alvin.sh                                                   # AlVin + CoxIter, for the cross-checks
```

The long runs were made under [`tools/memcap.sh`](tools/memcap.sh), a memory cap for macOS. The usage of each driver is in its docstring.
