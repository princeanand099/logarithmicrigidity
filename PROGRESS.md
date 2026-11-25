# Formalization Progress Record

- **Current Stage**: Complete dual-layer formalization finished, locked in `comparator`, and soundness-audited:
  1. `LogarithmicRigidity` (27 locked Mathlib-only theorems—including complete end-to-end affine non-dicriticality across all three elimination strata `x = 0`, `q₄(x) = 0`, `q₆(x) = 0`—with 0 custom axioms and 0 `sorry`s).
  2. `LogarithmicRigidityConditional` (all remaining manuscript theorems—Theorems 1.1, 1.2, 1.3(1)–(2), 1.4(1)–(2), Lemmas 2.1 & 3.1, Propositions 3.2 & 4.1—proved on top of `LogarithmicRigidity` and the minimal, sound, exact peer-reviewed external literature axioms in `LogarithmicRigidityConditional/ExternalLiterature.lean`).
- **Custom Axioms**:
  - `LogarithmicRigidity`: **0** (strictly `[propext, Classical.choice, Quot.sound]`).
  - `LogarithmicRigidityConditional`: Only the exact external peer-reviewed literature theorems documented in `EXTERNAL-AXIOMS.md` (all formulated over opaque geometric predicates with a consistent model). Zero manuscript-owned results are axiomatized.
- **Verification**: All modules imported by `LogarithmicRigidity.lean`, locked in `comparator/Challenge.lean` and `comparator.json`, and verified by GitHub Actions CI (`lake build LogarithmicRigidity`, `lake comparator`).
