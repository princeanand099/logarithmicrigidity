# Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations

Lean 4 (`v4.35.0`, Mathlib `v4.35.0`) formalization of algebraic, calculus, syzygy, elimination, and Positivstellensatz results from Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations*.

## Scope

Every theorem exported by `LogarithmicRigidity` and locked in `comparator/Challenge.lean` is proved directly on top of Mathlib `v4.35.0` using only the three standard Lean kernel axioms `[propext, Classical.choice, Quot.sound]`, with zero custom `axiom` declarations and zero hypothesis-bundle wrappers.

### Proved in This Repository
- **Section 2**: Euler projective identity for induced 1-forms (`induced_one_form_euler`), algebraic eigenvalue-ratio criterion of Lemma 2.1 (`lemma_2_1_tau_ratio_criterion`), monotonicity and superadditivity of `h` in Lemma 2.4 (`lemma_2_4_hBound_mono_superadd`).
- **Section 4**: Calculus core of Proposition 4.1 (`prop_4_1_local_first_integral_const`), proving via `HasDerivAt` and `Real.rpow` that `ũ(t) = f₁(t) ∏ |f_i(t)|^{λ_i/λ₁}` has zero derivative everywhere (including on `{f₁ = 0}`) and is constant along `C¹` orbits.
- **Section 5**:
  - Euler's Homogeneous Function Theorem on `MvPolynomial (Fin 3) ℂ` (`prop_5_1_euler_homogeneous`).
  - Proposition 5.1(1) exact algebraic correspondence between invariant 1-forms `ω = i_V i_E Ω` and Jacobian syzygies (`prop_5_1_syzygy_correspondence`).
  - Proposition 5.1(3) Koszul subspace correspondence with logarithmic pencil forms `ω_L = L dF - d F dL` (`prop_5_1_koszul_pencil_forms`).
  - Algebraic Koszul rigidity for Theorem 1.3(1): for any homogeneous `F ∈ ℂ[X, Y, Z]` of degree `d ≥ 2` whose Jacobian partial derivatives `(F_X, F_Y, F_Z)` form a regular sequence, every homogeneous degree-`(d - 1)` Jacobian syzygy lies in the 3-dimensional Koszul subspace (`theorem_1_3_part1_koszul_rigidity`).
  - Lemma 5.2 rational parametrization, affine smoothness away from `(0, 0)`, and smoothness along `L_∞` (`lemma_5_2_curve_Cm_geometry`, `lemma_5_2_Linf_smooth`).
  - Lemma 5.3 cofactor identity, origin blow-up eigenvalue inequality, and `Sing(ℱ_m(λ)) ∩ C_m ∩ L_∞ = ∅` (`lemma_5_3_foliation_Fm_cofactor_origin`, `lemma_5_3_Linf_disjoint`).
  - Proposition 5.4 parametrization factorization via `g_m(t; λ)`, nonvanishing of the linear `λ`-coefficient, and uncountability avoidance (`prop_5_4_param_factorization`, `prop_5_4_and_theorem_1_3_part2`).
- **Section 6 & Appendix A**:
  - Arithmetic inequalities for Theorem 1.4(1) (`hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound`).
  - Lemma 6.1 quartic geometry, Nullstellensatz singular locus `{(0, ±i)}`, compactness, separation along `x = 0`, IVT witness, and Hessian determinants `192 ∓ 32i ≠ 0` (`lemma_6_1_quartic_geometry`, `quartic_hessian_nodes`).
  - Proposition 6.2 `Sing(ℱ) ∩ L_∞ = ∅` (`sing_Linf_empty`), elimination `x * q₄(x) * q₆(x) ∈ ⟨P, Q⟩` (`sing_PQ_elim`), `x = 0` stratum (`sing_PQ_x_zero`), cofactor identity, and positivity certificates for `q₄`, `M₄`, `M₆` (`prop_6_2_counterexample_nondicritical`).
  - Proposition 6.3 & Theorem 1.4(2) SOS Positivstellensatz positivity of `H₁` and `H₂` (`prop_6_3_and_theorem_1_4_part2`) and Fundamental Theorem of Calculus proofs that `∫_0^T K(γ(t)) dt > 0` and `exp(∫_0^T K(γ(t)) dt) > 1` on both ovals (`floquet_integral_pos_oval1`, `floquet_integral_pos_oval2`).

### Not Proved (Missing Mathlib `v4.35.0` Foundations)
The full geometric statements of **Theorem 1.1**, **Theorem 1.2**, **Theorem 1.3(1)** (analytic dicriticality and Nullstellensatz/Bézout bridge), **Theorem 1.3(2)** (analytic perturbation branches `t_j(λ)`), and **Theorem 1.4(1)** are not formalized in this repository. They depend on six external theories not currently available in Mathlib `v4.35.0`:
1. Deligne (1971), *Théorie de Hodge II*, Cor. 3.2.14 (Kähler geometry and mixed Hodge theory for logarithmic 1-forms).
2. Carnicer (1994) / Seidenberg (1968) / Camacho–Sad (1982) (resolution of singularities of holomorphic foliations on complex surfaces and the proximity inequality).
3. Harnack (1876) and the normalization genus–`δ` formula (Riemann–Roch on smooth projective curves and real curve topology).
4. Coherent sheaf cohomology and Serre duality on `ℙ²` (Dimca 2013 syzygy–defect formula).
5. Camacho–Lins Neto–Sad (1984) local analytic normal forms for non-degenerate foliation singularities in `(ℂ², 0)`.
6. Giacomini–Llibre–Viano (1996) inverse integrating factor theorem for planar limit cycles and Christopher (2001) sharpness construction.

## Build & Verification

```bash
lake exe cache get
lake build LogarithmicRigidity Solution
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake comparator
```
