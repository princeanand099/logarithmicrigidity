/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs

/-!
# Locked Challenge Statements

This module locks the exact public theorem signatures verified against
`comparator/Solution.lean` via `lake comparator`. Every theorem here is proved
directly on top of Mathlib `v4.35.0` and `[propext, Classical.choice, Quot.sound]`,
with no custom axioms and no hypothesis-bundle structures. Only this file contains
intentional `sorry` stubs for `lake comparator`.
-/

namespace LogarithmicRigidity

/-- **Eq. (2.1)**: Euler's projective identity `X·A + Y·B + Z·C = 0`. -/
theorem induced_one_form_euler {R : Type*} [CommRing R] (ω : InducedOneForm R) :
    ω.X * ω.A + ω.Y * ω.B + ω.Z * ω.C = 0 := by
  sorry

/-- **Lemma 2.1**: Algebraic non-dicriticality criterion `τ = ρ + ρ⁻¹ + 2 ∉ [4, ∞) → ρ ∉ ℚ_{>0}`. -/
theorem lemma_2_1_tau_ratio_criterion (μ₁ μ₂ : ℂ) (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0) :
    let ρ := μ₁ / μ₂
    let τ := tauRatio (μ₁ + μ₂) (μ₁ * μ₂)
    τ = ρ + ρ⁻¹ + 2 ∧
    (InRealRayFour τ ↔ ρ.im = 0 ∧ 0 < ρ.re) ∧
    (IsNonDicriticalTau τ → ∀ q : ℚ, 0 < q → ρ ≠ (q : ℂ)) := by
  sorry

/-- **Lemma 2.4**: Monotonicity and superadditivity of the Harnack oval bound `h`. -/
theorem lemma_2_4_hBound_mono_superadd :
    (∀ d : ℕ, hBound d ≤ hBound (d + 1)) ∧
    (∀ a b : ℕ, hBound a + hBound b ≤ hBound (a + b)) ∧
    (∀ l : List ℕ, (l.map hBound).sum ≤ hBound l.sum) := by
  sorry

/-- **Proposition 4.1 (Calculus Core)**: Along any `C¹` orbit where `f_i(t) ≠ 0` (`i ∈ s`)
and the real logarithmic relation `λ₁ (∏ f_i) f₁' + ∑ λ_i f₁ (∏_{j≠i} f_j) f_i' = 0` holds,
the real-analytic local first integral `ũ(t) = f₁(t) ∏_{i ∈ s} |f_i(t)|^{λ_i / λ₁}` has
zero derivative everywhere (including on `f₁ = 0`) and is constant along orbits. -/
theorem prop_4_1_local_first_integral_const {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam₁ : ℝ) (hlam₁ : lam₁ ≠ 0) (lam : ι → ℝ)
    (f₁ f₁' : ℝ → ℝ) (f f' : ι → ℝ → ℝ)
    (hf₁ : ∀ t : ℝ, HasDerivAt f₁ (f₁' t) t)
    (hf : ∀ i ∈ s, ∀ t : ℝ, HasDerivAt (f i) (f' i t) t)
    (hne : ∀ i ∈ s, ∀ t : ℝ, f i t ≠ 0)
    (hlog : ∀ t : ℝ,
      lam₁ * (∏ j ∈ s, f j t) * f₁' t +
      ∑ i ∈ s, lam i * f₁ t * (∏ j ∈ s.erase i, f j t) * f' i t = 0) :
    ∀ t : ℝ,
      f₁ t * (∏ i ∈ s, |f i t| ^ (lam i / lam₁)) =
      f₁ 0 * (∏ i ∈ s, |f i 0| ^ (lam i / lam₁)) := by
  sorry

/-- **Proposition 5.1 (Euler's Homogeneous Function Theorem)**:
For any homogeneous `F : MvPolynomial (Fin 3) ℂ` of degree `d`,
`∑ i : Fin 3, X i * pderiv i F = d * F`. -/
theorem prop_5_1_euler_homogeneous (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i F = (d : MvPolynomial (Fin 3) ℂ) * F := by
  sorry

/-- **Proposition 5.1(1)**: Exact algebraic correspondence between invariant 1-forms
`ω = i_V i_E Ω` (`i_E ω = 0`, `ω ∧ dF ≡ 0 (mod F)`) and Jacobian syzygies `Syz(J_F)`. -/
theorem prop_5_1_syzygy_correspondence (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hd : 1 ≤ d) (hF : F.IsHomogeneous d) (hF_ne : F ≠ 0) :
    (∀ P₁ P₂ P₃ : MvPolynomial (Fin 3) ℂ,
      let ω := formOfSyzygy P₁ P₂ P₃
      MvPolynomial.X 0 * ω.1 + MvPolynomial.X 1 * ω.2.1 + MvPolynomial.X 2 * ω.2.2 = 0 ∧
      ω.1 * MvPolynomial.pderiv 1 F - ω.2.1 * MvPolynomial.pderiv 0 F =
        MvPolynomial.X 2 * (P₁ * MvPolynomial.pderiv 0 F + P₂ * MvPolynomial.pderiv 1 F +
          P₃ * MvPolynomial.pderiv 2 F) - (d : MvPolynomial (Fin 3) ℂ) * P₃ * F ∧
      ω.2.1 * MvPolynomial.pderiv 2 F - ω.2.2 * MvPolynomial.pderiv 1 F =
        MvPolynomial.X 0 * (P₁ * MvPolynomial.pderiv 0 F + P₂ * MvPolynomial.pderiv 1 F +
          P₃ * MvPolynomial.pderiv 2 F) - (d : MvPolynomial (Fin 3) ℂ) * P₁ * F ∧
      ω.2.2 * MvPolynomial.pderiv 0 F - ω.1 * MvPolynomial.pderiv 2 F =
        MvPolynomial.X 1 * (P₁ * MvPolynomial.pderiv 0 F + P₂ * MvPolynomial.pderiv 1 F +
          P₃ * MvPolynomial.pderiv 2 F) - (d : MvPolynomial (Fin 3) ℂ) * P₂ * F) ∧
    (∀ P₁ P₂ P₃ Q₁ Q₂ Q₃ : MvPolynomial (Fin 3) ℂ,
      IsJacobianSyzygy F P₁ P₂ P₃ → IsJacobianSyzygy F Q₁ Q₂ Q₃ →
      formOfSyzygy P₁ P₂ P₃ = formOfSyzygy Q₁ Q₂ Q₃ →
      P₁ = Q₁ ∧ P₂ = Q₂ ∧ P₃ = Q₃) ∧
    (∀ V₁ V₂ V₃ K : MvPolynomial (Fin 3) ℂ,
      V₁ * MvPolynomial.pderiv 0 F + V₂ * MvPolynomial.pderiv 1 F +
        V₃ * MvPolynomial.pderiv 2 F = K * F →
      ∃ P₁ P₂ P₃ : MvPolynomial (Fin 3) ℂ,
        IsJacobianSyzygy F P₁ P₂ P₃ ∧
        formOfSyzygy P₁ P₂ P₃ = formOfSyzygy V₁ V₂ V₃) := by
  sorry

/-- **Proposition 5.1(3)**: The 3-dimensional Koszul subspace corresponds precisely to the
logarithmic pencil forms `ω_L = L dF - (deg F) F dL`. -/
theorem prop_5_1_koszul_pencil_forms (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hF : F.IsHomogeneous d) (c₀ c₁ c₂ : ℂ) :
    let Fx := MvPolynomial.pderiv 0 F
    let Fy := MvPolynomial.pderiv 1 F
    let Fz := MvPolynomial.pderiv 2 F
    let L := MvPolynomial.C c₀ * MvPolynomial.X 0 +
             MvPolynomial.C c₁ * MvPolynomial.X 1 +
             MvPolynomial.C c₂ * MvPolynomial.X 2
    let P₁ := MvPolynomial.C c₁ * Fz - MvPolynomial.C c₂ * Fy
    let P₂ := MvPolynomial.C c₂ * Fx - MvPolynomial.C c₀ * Fz
    let P₃ := MvPolynomial.C c₀ * Fy - MvPolynomial.C c₁ * Fx
    IsJacobianSyzygy F P₁ P₂ P₃ ∧
    formOfSyzygy P₁ P₂ P₃ =
      (L * Fx - (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₀,
       L * Fy - (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₁,
       L * Fz - (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₂) := by
  sorry

/-- **Theorem 1.3(1) (Algebraic Koszul Rigidity)**: Whenever `(F_X, F_Y, F_Z)` is a regular
sequence in `ℂ[X, Y, Z]`, every homogeneous degree-`(d - 1)` Jacobian syzygy lies in the
3-dimensional Koszul subspace and induces a logarithmic pencil form `ω_L = L dF - d F dL`. -/
theorem theorem_1_3_part1_koszul_rigidity (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d)
    (hreg : IsRegularSeq3 (MvPolynomial.pderiv 0 F) (MvPolynomial.pderiv 1 F)
      (MvPolynomial.pderiv 2 F))
    (P₁ P₂ P₃ : MvPolynomial (Fin 3) ℂ)
    (hP₁ : P₁.IsHomogeneous (d - 1)) (hP₂ : P₂.IsHomogeneous (d - 1))
    (hP₃ : P₃.IsHomogeneous (d - 1))
    (hsyz : IsJacobianSyzygy F P₁ P₂ P₃) :
    ∃ c₀ c₁ c₂ : ℂ,
      P₁ = MvPolynomial.C c₁ * MvPolynomial.pderiv 2 F -
           MvPolynomial.C c₂ * MvPolynomial.pderiv 1 F ∧
      P₂ = MvPolynomial.C c₂ * MvPolynomial.pderiv 0 F -
           MvPolynomial.C c₀ * MvPolynomial.pderiv 2 F ∧
      P₃ = MvPolynomial.C c₀ * MvPolynomial.pderiv 1 F -
           MvPolynomial.C c₁ * MvPolynomial.pderiv 0 F ∧
      formOfSyzygy P₁ P₂ P₃ =
        ((MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 +
            MvPolynomial.C c₂ * MvPolynomial.X 2) * MvPolynomial.pderiv 0 F -
          (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₀,
         (MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 +
            MvPolynomial.C c₂ * MvPolynomial.X 2) * MvPolynomial.pderiv 1 F -
          (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₁,
         (MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 +
            MvPolynomial.C c₂ * MvPolynomial.X 2) * MvPolynomial.pderiv 2 F -
          (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₂) := by
  sorry

/-- **Lemma 5.2**: Geometry and rational parametrization of `C_m = {f_m = 0}` for all `m ≥ 2`. -/
theorem lemma_5_2_curve_Cm_geometry {m : ℕ} (hm : 2 ≤ m) :
    (∀ t : ℂ, 1 + 2 * t ^ (m + 1) ≠ 0 → fmPoly m (xParam m t) (yParam m t) = 0) ∧
    (∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) → fmDx m x y = 0 → fmDy m x y = 0 → fmPoly m x y ≠ 0) := by
  sorry

/-- **Lemma 5.2 (`L_∞` Smoothness)**: Along `L_∞`, `X^{m+1} + 2 Y^{m+1}` has no repeated
nonzero roots. -/
theorem lemma_5_2_Linf_smooth {m : ℕ} (hm : 2 ≤ m) (X Y : ℂ)
    (h0 : X ^ (m + 1) + 2 * Y ^ (m + 1) = 0)
    (hdx : ((m + 1 : ℕ) : ℂ) * X ^ m = 0) :
    X = 0 ∧ Y = 0 := by
  sorry

/-- **Lemma 5.3**: Exact cofactor identity and origin non-dicriticality of `ℱ_m(λ)` for
every `m ≥ 2` and `λ ∈ (0, 2(m + 1))`. -/
theorem lemma_5_3_foliation_Fm_cofactor_origin {m : ℕ} (hm : 2 ≤ m) :
    (∀ lam x y : ℂ,
      PmVec m lam x y * fmDx m x y + QmVec m lam x y * fmDy m x y =
        KmCof m lam x y * fmPoly m x y) ∧
    (∀ (lam : ℝ), 0 < lam → lam < 2 * ((m + 1 : ℕ) : ℝ) →
      ∀ ζ : ℂ, ζ ^ m = 1 →
        (-(1 : ℂ) / (m : ℂ) + (lam : ℂ) * ζ / (2 * (m : ℂ) * ((m + 1 : ℕ) : ℂ))).re < 0) := by
  sorry

/-- **Lemma 5.3 (`L_∞` Disjointness)**: `Sing(ℱ_m(λ)) ∩ C_m ∩ L_∞ = ∅`. -/
theorem lemma_5_3_Linf_disjoint {m : ℕ} (hm : 2 ≤ m) (lam X Y : ℂ)
    (hlam : lam ≠ 0) (hXY : X ≠ 0 ∨ Y ≠ 0)
    (hC : X ^ (m + 1) + 2 * Y ^ (m + 1) = 0) :
    lam * X ^ (m - 1) * Y ≠ 0 := by
  sorry

/-- **Proposition 5.4 (Parametrization Factorization)**: Exact factorization of `P_m` and `Q_m`
along `(x(t), y(t))` in terms of `g_m(t; λ)`. -/
theorem prop_5_4_param_factorization {m : ℕ} (hm : 2 ≤ m) (lam t : ℂ)
    (hden : 1 + 2 * t ^ (m + 1) ≠ 0) :
    PmVec m lam (xParam m t) (yParam m t) =
      -(xParam m t) ^ (m - 1) * (yParam m t - (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ))) *
        (t ^ (m - 1) / (1 + 2 * t ^ (m + 1))) * gmPoly m lam t ∧
    QmVec m lam (xParam m t) (yParam m t) =
      (xParam m t) ^ (m - 2) * (xParam m t + (m : ℂ) / ((m + 1 : ℕ) : ℂ)) *
        (xParam m t / (2 * (1 + 2 * t ^ (m + 1)))) * gmPoly m lam t := by
  sorry

/-- **Proposition 5.4 & Theorem 1.3(2)**: Nonvanishing of the linear `λ`-coefficient of `ρ_j(λ)`
at every root of `2 ω^{m+1} + 1 = 0` and existence of `λ ∈ (0, ε)` avoiding any countable
resonant set `E`. -/
theorem prop_5_4_and_theorem_1_3_part2 {m : ℕ} (hm : 2 ≤ m) :
    (∀ ω : ℂ, 2 * ω ^ (m + 1) + 1 = 0 → rhoLinearCoeff m ω ≠ 0) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ E : Set ℝ, E.Countable → ∃ lam ∈ Set.Ioo (0 : ℝ) ε, lam ∉ E) := by
  sorry

/-- **Lemma 6.1**: Geometry of the 2-nodal quartic `f(x, y) = 0` (6.1). -/
theorem lemma_6_1_quartic_geometry :
    (∀ X Y : ℝ, (X ≠ 0 ∨ Y ≠ 0) → 0 < quarticF4 X Y) ∧
    (∀ x y : ℂ, quarticF x y = 0 ∧ quarticFx x y = 0 ∧ quarticFy x y = 0 ↔
      x = 0 ∧ (y = Complex.I ∨ y = -Complex.I)) ∧
    (∀ y : ℝ, 0 < quarticF (0 : ℝ) y) ∧
    quarticF (-(1 : ℝ) / 2) 0 = 0 ∧
    (∃ ystar : ℝ, 0 < ystar ∧ ystar < 1 ∧ quarticF 1 ystar = 0) := by
  sorry

/-- **Lemma 6.1 (Hessian Determinants)**: Both singularities `(0, ±i)` are ordinary nodes
with nonzero Hessian determinants `192 ∓ 32i`. -/
theorem quartic_hessian_nodes :
    let fxx (x y : ℂ) := 24 * x ^ 2 + 6 * x - 4 * y ^ 2 + 2 * y - 16
    let fxy (x y : ℂ) := -8 * x * y + 2 * x
    let fyy (x y : ℂ) := -4 * x ^ 2 + 24 * y ^ 2 + 8
    (fxx 0 Complex.I * fyy 0 Complex.I - fxy 0 Complex.I ^ 2 = 192 - 32 * Complex.I) ∧
    (fxx 0 (-Complex.I) * fyy 0 (-Complex.I) - fxy 0 (-Complex.I) ^ 2 = 192 + 32 * Complex.I) ∧
    (fxx 0 Complex.I * fyy 0 Complex.I - fxy 0 Complex.I ^ 2 ≠ 0) ∧
    (fxx 0 (-Complex.I) * fyy 0 (-Complex.I) - fxy 0 (-Complex.I) ^ 2 ≠ 0) := by
  sorry

/-- **Proposition 6.2 (`L_∞`)**: `Sing(ℱ) ∩ L_∞ = ∅`. -/
theorem sing_Linf_empty (X Y : ℂ) (hXY : X ≠ 0 ∨ Y ≠ 0) :
    ¬ (48 * Y ^ 4 = 0 ∧ -(48 * X * Y ^ 3) = 0 ∧
      Y * (8 * X ^ 3 + 172 * X ^ 2 * Y + 48 * X * Y ^ 3 - 312 * Y ^ 3) -
      X * (320 * X ^ 3 + 16 * X ^ 2 * Y - 144 * X * Y ^ 2 + 48 * Y ^ 4) = 0) := by
  sorry

/-- **Proposition 6.2 (Elimination)**: Every complex affine singularity `(x, y)` of `(P, Q)`
satisfies `x = 0 ∨ q_4(x) = 0 ∨ q_6(x) = 0`. -/
theorem sing_PQ_elim (x y : ℂ) (hP : vecP x y = 0) (hQ : vecQ x y = 0) :
    x = 0 ∨ q4Poly x = 0 ∨ q6Poly x = 0 := by
  sorry

/-- **Proposition 6.2 (`x = 0` Stratum)**: At `x = 0`, the affine singularities are
precisely `(0, 0)` and `(0, ±i)`. -/
theorem sing_PQ_x_zero (y : ℂ) (hP : vecP 0 y = 0) (hQ : vecQ 0 y = 0) :
    y = 0 ∨ y = Complex.I ∨ y = -Complex.I := by
  sorry

/-- **Proposition 6.2 (Cofactor, Positivity & Non-Dicriticality Certificates)**:
Cofactor identity, strict positivity of `q_4` and `M_4` on `ℝ`, strict positivity of
`M_6` on `[4, ∞)`, and `τ ∉ [4, ∞)` at `(0, 0)` and `(0, ±i)`. -/
theorem prop_6_2_counterexample_nondicritical :
    (∀ x y : ℂ, vecP x y * quarticFx x y + vecQ x y * quarticFy x y =
      cofactorK x y * quarticF x y) ∧
    (∀ x : ℝ, 0 < q4Poly x) ∧
    (∀ τ : ℝ, 0 < M4Poly τ) ∧
    (∀ τ : ℝ, 4 ≤ τ → 0 < M6Poly τ) ∧
    IsNonDicriticalTau (tauRatio (jacTr 0 0) (jacDet 0 0)) ∧
    IsNonDicriticalTau (tauRatio (jacTr 0 Complex.I) (jacDet 0 Complex.I)) ∧
    IsNonDicriticalTau (tauRatio (jacTr 0 (-Complex.I)) (jacDet 0 (-Complex.I))) := by
  sorry

/-- **Proposition 6.2 (No Real Singularities on the Quartic)**: Neither real oval of the
2-nodal quartic `f(x, y) = 0` (6.1) contains any singularity of `(P, Q)` (6.2). -/
theorem prop_6_2_no_real_singularity_on_quartic (x y : ℝ)
    (hf : quarticF x y = 0) : ¬ (vecP x y = 0 ∧ vecQ x y = 0) := by
  sorry

/-- **Proposition 6.2 (`q₄` Stratum Non-Dicriticality)**: Every complex affine singularity
`(x, y)` of `(P, Q)` (6.2) with `q₄(x) = 0` is non-degenerate and satisfies `τ(x, y) ∉ [4, ∞)`. -/
theorem prop_6_2_q4_stratum_nondicritical (x y : ℂ)
    (hP : vecP x y = 0) (hQ : vecQ x y = 0) (hq : q4Poly x = 0) :
    jacDet x y ≠ 0 ∧ IsNonDicriticalTau (tauRatio (jacTr x y) (jacDet x y)) := by
  sorry

/-- **Proposition 6.2 (`q₆` Stratum Non-Dicriticality)**: Every complex affine singularity
`(x, y)` of `(P, Q)` (6.2) with `q₆(x) = 0` is non-degenerate and satisfies `τ(x, y) ∉ [4, ∞)`. -/
theorem prop_6_2_q6_stratum_nondicritical (x y : ℂ)
    (hP : vecP x y = 0) (hQ : vecQ x y = 0) (hq : q6Poly x = 0) :
    jacDet x y ≠ 0 ∧ IsNonDicriticalTau (tauRatio (jacTr x y) (jacDet x y)) := by
  sorry

/-- **Proposition 6.2 (Complete End-to-End Affine Non-Dicriticality Certification)**:
Every complex affine singularity `(x, y)` of `(P, Q)` (6.2) across all three strata is
non-degenerate (`jacDet x y ≠ 0`) and satisfies `τ(x, y) ∉ [4, ∞)`. -/
theorem prop_6_2_all_affine_singularities_nondicritical (x y : ℂ)
    (hP : vecP x y = 0) (hQ : vecQ x y = 0) :
    jacDet x y ≠ 0 ∧ IsNonDicriticalTau (tauRatio (jacTr x y) (jacDet x y)) := by
  sorry

/-- **Proposition 6.3 & Theorem 1.4(2) (Positivstellensatz Core)**: Strict positivity of
`H₁` on `{f = 0, x < 0}` and `H₂` on `{f = 0, x > 0}`, and `H_nodal(3) < 2`. -/
theorem prop_6_3_and_theorem_1_4_part2 :
    (∀ x y : ℝ, quarticF x y = 0 → x < 0 → 0 < H1Scaled x y) ∧
    (∀ x y : ℝ, quarticF x y = 0 → 0 < x → 0 < H2Scaled x y) ∧
    (∀ y : ℝ, 0 ≤ y → y ≤ 1 → 0 < H2Scaled 1 y) ∧
    Hnodal 3 < 2 := by
  sorry

/-- **Proposition 6.3 (Floquet Integral via FTC on Oval 1)**:
Any `C¹` periodic orbit `(x(t), y(t))` of `(P, Q)` on `{f = 0, x < 0}` has strictly
positive Floquet integral `∫_0^T K(γ(t)) dt > 0` and repelling multiplier `> 1`. -/
theorem floquet_integral_pos_oval1 (T : ℝ) (hT : 0 < T) (x y : ℝ → ℝ)
    (hx : ∀ t ∈ Set.uIcc 0 T, HasDerivAt x (vecP (x t) (y t)) t)
    (hy : ∀ t ∈ Set.uIcc 0 T, HasDerivAt y (vecQ (x t) (y t)) t)
    (hper_x : x T = x 0) (hper_y : y T = y 0)
    (hon : ∀ t ∈ Set.Icc 0 T, quarticF (x t) (y t) = 0 ∧ x t < 0)
    (hcont_x : ContinuousOn x (Set.uIcc 0 T)) (hcont_y : ContinuousOn y (Set.uIcc 0 T)) :
    0 < ∫ t in (0 : ℝ)..T, cofactorK (x t) (y t) ∧
    1 < Real.exp (∫ t in (0 : ℝ)..T, cofactorK (x t) (y t)) := by
  sorry

/-- **Proposition 6.3 (Floquet Integral via FTC on Oval 2)**:
Any `C¹` periodic orbit `(x(t), y(t))` of `(P, Q)` on `{f = 0, x > 0}` has strictly
positive Floquet integral `∫_0^T K(γ(t)) dt > 0` and repelling multiplier `> 1`. -/
theorem floquet_integral_pos_oval2 (T : ℝ) (hT : 0 < T) (x y : ℝ → ℝ)
    (hx : ∀ t ∈ Set.uIcc 0 T, HasDerivAt x (vecP (x t) (y t)) t)
    (hy : ∀ t ∈ Set.uIcc 0 T, HasDerivAt y (vecQ (x t) (y t)) t)
    (hper_x : x T = x 0) (hper_y : y T = y 0)
    (hon : ∀ t ∈ Set.Icc 0 T, quarticF (x t) (y t) = 0 ∧ 0 < x t)
    (hcont_x : ContinuousOn x (Set.uIcc 0 T)) (hcont_y : ContinuousOn y (Set.uIcc 0 T)) :
    0 < ∫ t in (0 : ℝ)..T, cofactorK (x t) (y t) ∧
    1 < Real.exp (∫ t in (0 : ℝ)..T, cofactorK (x t) (y t)) := by
  sorry

end LogarithmicRigidity
