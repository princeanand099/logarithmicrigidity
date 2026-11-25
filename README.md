# Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations

Lean 4 (`v4.35.0`) formalization of the **unconditional Mathlib-only** algebraic, calculus, elimination, and Positivstellensatz results of Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations*.

## Strict Scope & Honesty Statement

- **Zero custom axioms, zero hypothesis-bundle shortcuts**: Every theorem exported in `LogarithmicRigidity` and locked in `comparator/Challenge.lean` is proved **100% unconditionally on top of Mathlib `v4.35.0`** and the 3 standard Lean axioms `[propext, Classical.choice, Quot.sound]`.
- **What is PROVED unconditionally**:
  - **§2**: Eq. (2.1) Euler identity (`induced_one_form_euler`), Lemma 2.1 algebraic criterion (`lemma_2_1_tau_ratio_criterion`), Lemma 2.4 monotonicity and superadditivity of `h` (`lemma_2_4_hBound_mono_superadd`).
  - **§4**: Proposition 4.1 $C^1$ local first-integral invariance (`prop_4_1_local_first_integral_const`: `ũ(t) = f₁(t) ∏ |f_i(t)|^{λ_i/λ₁}` has zero derivative everywhere, including on `f₁ = 0`, and is constant along orbits).
  - **§5**: Proposition 5.1 Euler's Homogeneous Function Theorem on `MvPolynomial (Fin 3) ℂ` (`prop_5_1_euler_homogeneous`), Lemma 5.2 rational parametrization and non-singularity of `C_m` (`lemma_5_2_curve_Cm_geometry`), Lemma 5.3 cofactor identity and origin non-dicriticality (`lemma_5_3_foliation_Fm_cofactor_origin`), Proposition 5.4 & Theorem 1.3(2) nonvanishing linear `λ`-coefficient and uncountability avoidance (`prop_5_4_and_theorem_1_3_part2`).
  - **§6 & Appendix A**: Arithmetic bounds for Theorem 1.4(1) (`hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound`), Lemma 6.1 quartic geometry & exact Nullstellensatz singular locus `{(0, ±i)}` (`lemma_6_1_quartic_geometry`) + Hessian determinants `192 ∓ 32i ≠ 0` (`quartic_hessian_nodes`), Proposition 6.2 `Sing(ℱ) ∩ L_∞ = ∅` (`sing_Linf_empty`), exact integer elimination `x * q₄(x) * q₆(x) ∈ ⟨P, Q⟩` (`sing_PQ_elim`), `x = 0` stratum (`sing_PQ_x_zero`), cofactor & SOS/shifted positivity certificates (`prop_6_2_counterexample_nondicritical`), Proposition 6.3 & Theorem 1.4(2) exact rational SOS Positivstellensatz certificates for `H₁ > 0` on `{f = 0, x < 0}` and `H₂ > 0` on `{f = 0, x > 0}` (`prop_6_3_and_theorem_1_4_part2`), and unconditional Fundamental Theorem of Calculus proofs that `∫_0^T K(γ(t)) dt > 0` and `exp(∫_0^T K(γ(t)) dt) > 1` on both ovals (`floquet_integral_pos_oval1`, `floquet_integral_pos_oval2`).
- **What is NOT formalized (open Mathlib prerequisites)**:
  - Theorems 1.1, 1.2, 1.3(1), and 1.4(1) in full geometric generality are **not** formalized, because Mathlib `v4.35.0` does not yet contain the 6 deep external theories they depend on: Deligne's *Théorie de Hodge II* (Kähler/mixed Hodge theory), Carnicer's theorem (Seidenberg resolution + Camacho–Sad index theorem), Harnack's curve theorem (Riemann–Roch + normalization genus–$\delta$ formula), Serre duality for coherent sheaves on $\mathbb{P}^2$, Camacho–Lins Neto–Sad local analytic normal forms, and Giacomini–Llibre–Viano / Christopher planar Poincaré-return-map theory. Rather than faking these theorems with hypothesis wrappers, they are omitted until those Mathlib foundations exist.

## Build & Verification

```bash
lake exe cache get
lake build LogarithmicRigidity Solution
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake comparator
```
