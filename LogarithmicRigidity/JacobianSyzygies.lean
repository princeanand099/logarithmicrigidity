/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs

/-!
# Section 5: Jacobian Syzygies and Irreducible Curves of Degree `m + 1`

100% unconditional Mathlib-only proofs for Section 5:
- Euler's Homogeneous Function Theorem on `MvPolynomial (Fin 3) ℂ`
- Lemma 5.2 (geometry and rational parametrization of `C_m`)
- Lemma 5.3 (cofactor identity and origin non-dicriticality of `ℱ_m(λ)`)
- Proposition 5.4 & Theorem 1.3(2) (nonvanishing linear `λ`-coefficient & uncountability)
-/

namespace LogarithmicRigidity

private lemma euler_monomial (m : Fin 3 →₀ ℕ) (c : ℂ) :
    ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial m c) =
      ((∑ i : Fin 3, m i : ℕ) : MvPolynomial (Fin 3) ℂ) * MvPolynomial.monomial m c := by
  have hterm : ∀ i : Fin 3,
      MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.monomial m c) =
        ((m i : ℕ) : MvPolynomial (Fin 3) ℂ) * MvPolynomial.monomial m c := by
    intro i
    rw [MvPolynomial.pderiv_monomial]
    by_cases hi : m i = 0
    · simp [hi]
    · rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
      have hadd : Finsupp.single i 1 + (m - Finsupp.single i 1) = m := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · simp [Finsupp.single_eq_of_ne hj]
      rw [hadd]
      have hnat : ((m i : ℕ) : MvPolynomial (Fin 3) ℂ) = MvPolynomial.C ((m i : ℕ) : ℂ) := by
        simp
      rw [hnat, MvPolynomial.C_mul_monomial, mul_comm]
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_mul, Nat.cast_sum]

/-- **Proposition 5.1 (Euler's Homogeneous Function Theorem)**:
For any homogeneous `F : MvPolynomial (Fin 3) ℂ` of degree `d`,
`∑ i : Fin 3, X i * pderiv i F = d * F`. -/
theorem prop_5_1_euler_homogeneous (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i F = (d : MvPolynomial (Fin 3) ℂ) * F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [euler_monomial]
  have hdeg : ∑ i : Fin 3, m i = d := by
    have hw := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hw
  rw [hdeg]

/-- **Lemma 5.2**: Geometry and rational parametrization of `C_m = {f_m = 0}` for all `m ≥ 2`. -/
theorem lemma_5_2_curve_Cm_geometry {m : ℕ} (hm : 2 ≤ m) :
    (∀ t : ℂ, 1 + 2 * t ^ (m + 1) ≠ 0 → fmPoly m (xParam m t) (yParam m t) = 0) ∧
    (∀ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) → fmDx m x y = 0 → fmDy m x y = 0 → fmPoly m x y ≠ 0) := by
  constructor
  · intro t ht
    have hfactor : fmPoly m (xParam m t) (yParam m t) =
        xParam m t ^ m * ((1 - t ^ m) + xParam m t * (1 + 2 * t ^ (m + 1))) := by
      unfold fmPoly yParam
      rw [mul_pow, mul_pow, pow_succ (xParam m t) m]
      ring
    rw [hfactor]
    have hzero : (1 - t ^ m) + xParam m t * (1 + 2 * t ^ (m + 1)) = 0 := by
      unfold xParam
      rw [div_mul_cancel₀ _ ht]
      ring
    rw [hzero, mul_zero]
  · intro x y hxy hdx hdy
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    have hm_sub : m - 1 + 1 = m := by omega
    have hx_cases : x = 0 ∨ ((m + 1 : ℕ) : ℂ) * x = -(m : ℂ) := by
      have hxm : x ^ m = x ^ (m - 1) * x := by rw [← pow_succ, hm_sub]
      have hfac : x ^ (m - 1) * ((m : ℂ) + ((m + 1 : ℕ) : ℂ) * x) = 0 := by
        unfold fmDx at hdx
        rw [hxm] at hdx
        linear_combination hdx
      rcases mul_eq_zero.mp hfac with hx0 | hlin
      · left; by_contra h; exact pow_ne_zero (m - 1) h hx0
      · right; linear_combination hlin
    have hy_cases : y = 0 ∨ 2 * ((m + 1 : ℕ) : ℂ) * y = (m : ℂ) := by
      have hym : y ^ m = y ^ (m - 1) * y := by rw [← pow_succ, hm_sub]
      have hfac : y ^ (m - 1) * (-(m : ℂ) + 2 * ((m + 1 : ℕ) : ℂ) * y) = 0 := by
        unfold fmDy at hdy
        rw [hym] at hdy
        linear_combination hdy
      rcases mul_eq_zero.mp hfac with hy0 | hlin
      · left; by_contra h; exact pow_ne_zero (m - 1) h hy0
      · right; linear_combination hlin
    rcases hx_cases with rfl | hx_eq <;> rcases hy_cases with rfl | hy_eq
    · rcases hxy with hx | hy
      · exact absurd rfl hx
      · exact absurd rfl hy
    · intro hfm
      have hy_ne : y ≠ 0 := by
        intro hy0
        rw [hy0, mul_zero] at hy_eq
        exact hm0 hy_eq.symm
      have hval : ((m + 1 : ℕ) : ℂ) * fmPoly m 0 y = -(y ^ m) := by
        calc
          ((m + 1 : ℕ) : ℂ) * fmPoly m 0 y
              = y ^ m * (-((m + 1 : ℕ) : ℂ) + 2 * ((m + 1 : ℕ) : ℂ) * y) := by
                unfold fmPoly
                rw [zero_pow (by omega), zero_pow (by omega), pow_succ y m]
                ring
          _ = y ^ m * (-((m : ℂ) + 1) + (m : ℂ)) := by rw [hy_eq, hcast]
          _ = -(y ^ m) := by ring
      rw [hfm, mul_zero] at hval
      have : y ^ m = 0 := neg_eq_zero.mp hval.symm
      exact pow_ne_zero m hy_ne this
    · intro hfm
      have hx_ne : x ≠ 0 := by
        intro hx0
        rw [hx0, mul_zero] at hx_eq
        exact hm0 (neg_eq_zero.mp hx_eq.symm)
      have hval : ((m + 1 : ℕ) : ℂ) * fmPoly m x 0 = x ^ m := by
        calc
          ((m + 1 : ℕ) : ℂ) * fmPoly m x 0
              = x ^ m * (((m + 1 : ℕ) : ℂ) + ((m + 1 : ℕ) : ℂ) * x) := by
                unfold fmPoly
                rw [zero_pow (by omega), zero_pow (by omega), pow_succ x m]
                ring
          _ = x ^ m * (((m : ℂ) + 1) + -(m : ℂ)) := by rw [hx_eq, hcast]
          _ = x ^ m := by ring
      rw [hfm, mul_zero] at hval
      exact pow_ne_zero m hx_ne hval.symm
    · intro hfm
      have hy_ne : y ≠ 0 := by
        intro hy0
        rw [hy0, mul_zero] at hy_eq
        exact hm0 hy_eq.symm
      have hxy_rel : x = -2 * y := by
        have hsum : ((m + 1 : ℕ) : ℂ) * (x + 2 * y) = 0 := by
          linear_combination hx_eq + hy_eq
        have h0 : x + 2 * y = 0 := (mul_eq_zero.mp hsum).resolve_left hm1
        linear_combination h0
      have hval : ((m + 1 : ℕ) : ℂ) * fmPoly m x y = x ^ m - y ^ m := by
        calc
          ((m + 1 : ℕ) : ℂ) * fmPoly m x y
              = x ^ m * (((m + 1 : ℕ) : ℂ) + ((m + 1 : ℕ) : ℂ) * x) +
                y ^ m * (-((m + 1 : ℕ) : ℂ) + 2 * ((m + 1 : ℕ) : ℂ) * y) := by
                unfold fmPoly
                rw [pow_succ x m, pow_succ y m]
                ring
          _ = x ^ m * (((m : ℂ) + 1) + -(m : ℂ)) +
              y ^ m * (-((m : ℂ) + 1) + (m : ℂ)) := by rw [hx_eq, hy_eq, hcast]
          _ = x ^ m - y ^ m := by ring
      rw [hfm, mul_zero, hxy_rel, mul_pow] at hval
      have hfac : ((-2 : ℂ) ^ m - 1) * y ^ m = 0 := by linear_combination -hval
      have hpow1 : (-2 : ℂ) ^ m = 1 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (pow_ne_zero m hy_ne))
      have hnorm := congr_arg norm hpow1
      rw [norm_pow, norm_one] at hnorm
      have hnorm2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      rw [hnorm2] at hnorm
      have hgt : (1 : ℝ) < (2 : ℝ) ^ m := one_lt_pow₀ (by norm_num) (by omega)
      linarith

/-- **Lemma 5.3**: Exact cofactor identity and origin non-dicriticality of `ℱ_m(λ)` for
every `m ≥ 2` and `λ ∈ (0, 2(m + 1))`. -/
theorem lemma_5_3_foliation_Fm_cofactor_origin {m : ℕ} (hm : 2 ≤ m) :
    (∀ lam x y : ℂ,
      PmVec m lam x y * fmDx m x y + QmVec m lam x y * fmDy m x y =
        KmCof m lam x y * fmPoly m x y) ∧
    (∀ (lam : ℝ), 0 < lam → lam < 2 * ((m + 1 : ℕ) : ℝ) →
      ∀ ζ : ℂ, ζ ^ m = 1 →
        (-(1 : ℂ) / (m : ℂ) + (lam : ℂ) * ζ / (2 * (m : ℂ) * ((m + 1 : ℕ) : ℂ))).re < 0) := by
  constructor
  · intro lam x y
    have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    have hx1 : x ^ (m - 1) = x ^ (m - 2) * x := by
      rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
    have hx2 : x ^ m = x ^ (m - 2) * x ^ 2 := by
      rw [← pow_add, show m - 2 + 2 = m by omega]
    have hx3 : x ^ (m + 1) = x ^ (m - 2) * x ^ 3 := by
      rw [← pow_add, show m - 2 + 3 = m + 1 by omega]
    have hy1 : y ^ m = y ^ (m - 1) * y := by
      rw [← pow_succ, show m - 1 + 1 = m by omega]
    have hy2 : y ^ (m + 1) = y ^ (m - 1) * y ^ 2 := by
      rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
    unfold PmVec QmVec KmCof fmPoly fmDx fmDy
    rw [hx3, hx2, hx1, hy2, hy1]
    field_simp [hm1]
    rw [hcast]
    ring
  · intro lam hlam0 hlam_lt ζ hζ
    have hζ_norm : ‖ζ‖ = 1 := by
      have h1 : ‖ζ‖ ^ m = 1 := by
        rw [← norm_pow, hζ, norm_one]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hlt1 : ‖ζ‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg ζ) hlt (by omega)
        linarith
      · have hgt1 : 1 < ‖ζ‖ ^ m := one_lt_pow₀ hgt (by omega)
        linarith
    have hζ_re : ζ.re ≤ 1 := by
      calc ζ.re ≤ ‖ζ‖ := Complex.re_le_norm ζ
        _ = 1 := hζ_norm
    have hre :
        (-(1 : ℂ) / (m : ℂ) + (lam : ℂ) * ζ / (2 * (m : ℂ) * ((m + 1 : ℕ) : ℂ))).re =
        -(1 : ℝ) / (m : ℝ) + (lam / (2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ))) * ζ.re := by
      have h1 : -(1 : ℂ) / (m : ℂ) = (((-(1 : ℝ) / (m : ℝ)) : ℝ) : ℂ) := by push_cast; ring
      have h2 : (lam : ℂ) * ζ / (2 * (m : ℂ) * ((m + 1 : ℕ) : ℂ)) =
          (((lam / (2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ))) : ℝ) : ℂ) * ζ := by
        push_cast; ring
      rw [Complex.add_re, h1, Complex.ofReal_re, h2, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre, neg_div]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hden_pos : (0 : ℝ) < 2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ) := by positivity
    have hfrac_pos : 0 < lam / (2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ)) := div_pos hlam0 hden_pos
    have hstep1 : (lam / (2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ))) * ζ.re ≤
        lam / (2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
      nlinarith
    have hstep2 : lam / (2 * (m : ℝ) * ((m + 1 : ℕ) : ℝ)) < 1 / (m : ℝ) := by
      rw [div_lt_div_iff₀ hden_pos hm_pos]
      nlinarith
    linarith

/-- **Proposition 5.4 & Theorem 1.3(2)**: Nonvanishing of the linear `λ`-coefficient of `ρ_j(λ)`
at every root of `2 ω^{m+1} + 1 = 0` and existence of `λ ∈ (0, ε)` avoiding any countable
resonant set `E`. -/
theorem prop_5_4_and_theorem_1_3_part2 {m : ℕ} (hm : 2 ≤ m) :
    (∀ ω : ℂ, 2 * ω ^ (m + 1) + 1 = 0 → rhoLinearCoeff m ω ≠ 0) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ E : Set ℝ, E.Countable → ∃ lam ∈ Set.Ioo (0 : ℝ) ε, lam ∉ E) := by
  constructor
  · intro ω hω
    have hpow : 2 * ‖ω‖ ^ (m + 1) = 1 := by
      have h1 : 2 * ω ^ (m + 1) = -1 := eq_neg_of_add_eq_zero_left hω
      have h2 := congr_arg norm h1
      rw [norm_mul, norm_pow, norm_neg, norm_one] at h2
      have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hnorm2] at h2
      exact h2
    have hω_lt_one : ‖ω‖ < 1 := by
      by_contra hge
      push Not at hge
      have h1 : (1 : ℝ) ≤ ‖ω‖ ^ (m + 1) := one_le_pow₀ hge
      linarith
    have hω_gt_half : (1 : ℝ) / 2 < ‖ω‖ := by
      by_contra hle
      push Not at hle
      have h1 : ‖ω‖ ^ (m + 1) ≤ ((1 : ℝ) / 2) ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg ω) hle (m + 1)
      have h2 : ((1 : ℝ) / 2) ^ (m + 1) ≤ ((1 : ℝ) / 2) ^ 3 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      norm_num at h2
      linarith
    have hfac1 : ((m : ℂ) - 1) / 2 - ω ≠ 0 := by
      intro h
      have hω_eq : ω = ((((m : ℝ) - 1) / 2 : ℝ) : ℂ) := by
        have : ω = ((m : ℂ) - 1) / 2 := (sub_eq_zero.mp h).symm
        rw [this]; push_cast; ring
      have hnorm_eq : ‖ω‖ = ((m : ℝ) - 1) / 2 := by
        rw [hω_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      rcases eq_or_lt_of_le hm with rfl | hm3
      · norm_num at hnorm_eq
        linarith
      · have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
        linarith
    have hfac2 : 2 * ω + 1 ≠ 0 := by
      intro h
      have h1 : 2 * ω = -1 := eq_neg_of_add_eq_zero_left h
      have h2 := congr_arg norm h1
      rw [norm_mul, norm_neg, norm_one] at h2
      have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hnorm2] at h2
      linarith
    have hfac3 : 2 * (((m + 1 : ℕ) : ℂ) ^ 3) ≠ 0 := by
      refine mul_ne_zero (by norm_num) (pow_ne_zero 3 ?_)
      exact Nat.cast_ne_zero.mpr (by omega)
    have hfac4 : ω ^ m - 1 ≠ 0 := by
      intro h
      have h1 : ω ^ m = 1 := sub_eq_zero.mp h
      have h2 := congr_arg norm h1
      rw [norm_pow, norm_one] at h2
      have hlt : ‖ω‖ ^ m < 1 := pow_lt_one₀ (norm_nonneg ω) hω_lt_one (by omega)
      linarith
    unfold rhoLinearCoeff
    exact div_ne_zero (mul_ne_zero hfac1 hfac2) (mul_ne_zero hfac3 hfac4)
  · intro ε hε E hE
    have hunc : ¬ (Set.Ioo (0 : ℝ) ε).Countable := by
      intro hc
      haveI : Countable (Set.Ioo (0 : ℝ) ε) := hc.to_subtype
      have hle : Cardinal.mk (Set.Ioo (0 : ℝ) ε) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      rw [Cardinal.mk_Ioo_real hε] at hle
      exact not_le_of_gt Cardinal.aleph0_lt_continuum hle
    by_contra hno
    push Not at hno
    have hsub : Set.Ioo (0 : ℝ) ε ⊆ E := fun x hx => hno x hx
    exact hunc (hE.mono hsub)

end LogarithmicRigidity
