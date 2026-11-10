# reflect-zphi

**This project is the one specified in `TASK.md`:** the rank-3 strongly squarefree (SSF) reflective hyperbolic lattices over ℤ[φ].

The `CLAUDE.md` in the parent directory (`/Users/jam/dev/sandbox/`) describes an unrelated Bianchi-extension/AlVin test suite. **It does not apply here.**

- **Code** (Python, PARI, C, Lean) lives in this repository.
- **The manuscript** lives in the sibling folder `../reflect-zphi-paper/`.

Read these first:

- `TASK.md`: the brief, the gates and the mandatory stop points.
- `methods.md`: the technology choices, conventions and pipeline.
- `lean-plan.md`: the Lean development and its trusted computing base.
- `OPEN_QUESTIONS.md`, `DISCREPANCIES.md`: unresolved doubts, which must never be assumed away.
- `notes/`: the supplied step-1 and step-2 notes.
- `prototype/`: the supplied Python prototype. It is the test oracle; **do not edit it**.

Ground rules (from TASK.md §4):

- Exact arithmetic only.
- Commit after each gate.
- Stop and report at the mandated stop points.
- **Lean is kernel-only:** no `native_decide`, no `sorry`, and no axioms beyond the approved imported-theorem list.
