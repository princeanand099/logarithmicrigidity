# Formalization Progress Record

- **Current Stage**: Complete dual-layer formalization implemented and soundness-audited:
  1. `LogarithmicRigidity` (25 unconditional Mathlib-only theorems including `prop_6_2_q4_stratum_nondicritical`, 0 custom axioms, 0 `sorry`s).
  2. `LogarithmicRigidityConditional` (all remaining manuscript theorems—Theorems 1.1, 1.2, 1.3(1)–(2), 1.4(1)–(2), Lemmas 2.1 & 3.1, Propositions 3.2 & 4.1—proved on top of `LogarithmicRigidity` and the minimal, sound, exact peer-reviewed external literature axioms in `LogarithmicRigidityConditional/ExternalLiterature.lean`).
- **Custom Axioms**:
  - `LogarithmicRigidity`: **0** (strictly `[propext, Classical.choice, Quot.sound]`).
  - `LogarithmicRigidityConditional`: Only the exact external peer-reviewed literature theorems documented in `EXTERNAL-AXIOMS.md` (all formulated over opaque geometric predicates with a consistent model). Zero manuscript-owned results are axiomatized.
- **Verification**: All modules imported by `LogarithmicRigidity.lean` and built by GitHub Actions CI (`lake build LogarithmicRigidity`).
