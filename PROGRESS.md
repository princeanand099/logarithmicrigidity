# Formalization Progress Record

- **Current Stage**: Batch 1 (`SyzygyKoszul.lean` + deprecation fix + honest documentation overhaul) pushed; preparing Batch 2 (`Section6FullCert.lean` end-to-end Gröbner/Bézout/Horner bridge for Proposition 6.2).
- **Custom Axioms**: 0 (strictly `[propext, Classical.choice, Quot.sound]`).
- **Active Modules (all imported by `LogarithmicRigidity.lean`)**:
  - `LogarithmicRigidity/Preliminaries.lean` — Eq. (2.1), Lemma 2.1, Lemma 2.4
  - `LogarithmicRigidity/RealLogarithmicCalculus.lean` — Prop. 4.1 (`C¹` local first integral invariance)
  - `LogarithmicRigidity/JacobianSyzygies.lean` — Prop. 5.1 (Euler identity), Lemma 5.2, Lemma 5.3, Prop. 5.4 & Thm 1.3(2)
  - `LogarithmicRigidity/SyzygyKoszul.lean` — Prop. 5.1(1)/(3), Thm 1.3(1) algebraic Koszul rigidity, Lemma 5.2 & 5.3 `L_∞`, Prop. 5.4 parametrization factorization
  - `LogarithmicRigidity/CaseRNonZero.lean` — Thm 1.4(1) arithmetic bounds, Lemma 6.1
  - `LogarithmicRigidity/CounterexampleCert.lean` — Prop. 6.2 (cofactor, SOS `q₄`/`M₄`, shifted `M₆`), Prop. 6.3 & Thm 1.4(2) (SOS Positivstellensatz `H₁`/`H₂`)
  - `LogarithmicRigidity/Section6ElimCert.lean` — Lemma 6.1 Hessians, Prop. 6.2 (`L_∞`, `x * q₄ * q₆ ∈ ⟨P, Q⟩`, `x = 0` stratum), Prop. 6.3 (FTC Floquet integrals)
  - `LogarithmicRigidity/SanityChecks.lean` & `LogarithmicRigidity/AuditAxioms.lean`
- **Not Formalized**: Full geometric Theorems 1.1, 1.2, 1.3(1), and 1.4(1), which depend on 6 classical theories absent from Mathlib `v4.35.0` (Deligne 1971, Carnicer 1994, Harnack 1876, Serre duality on `ℙ²`, Camacho–Lins Neto–Sad 1984, Giacomini–Llibre–Viano 1996).
