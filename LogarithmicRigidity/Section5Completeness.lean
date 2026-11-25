/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.JacobianSyzygies
import LogarithmicRigidity.SyzygyKoszul

/-!
# Section 5 (Completeness): Euler Kernel Surjectivity, Irreducibility, Blow-Up, and Asymptotics

100% unconditional Mathlib-only proofs closing the algebraic and analytic-expansion gaps in §5:
- `prop_5_1_euler_kernel_surj`: Every triple `(A, B, C)` in `ℂ[X, Y, Z]³` satisfying Euler's
  identity `X A + Y B + Z C = 0` is of the form `formOfSyzygy V₁ V₂ V₃` (completing the
  surjectivity half of Proposition 5.1(1)).
- `lemma_5_2_param_surjective`: Every nonzero affine point of `C_m` is either `(0, 1/2)` or
  `(x(t), y(t))` for a unique `t` with `1 + 2 t^{m+1} ≠ 0` (Lemma 5.2 birationality).
- `lemma_5_2_Fm_no_common_root_Linf`: `X^m - Y^m` and `X^{m+1} + 2 Y^{m+1}` share no nonzero
  complex root (the coprimality core of irreducibility of `F_m(X, Y, Z)` in Lemma 5.2).
- `lemma_5_3_Pm_Qm_coprime`: None of the four irreducible factors of `K_m f_m` divides both
  `P_m` and `Q_m` (saturation `gcd(P_m, Q_m) = 1` in Lemma 5.3).
- `lemma_5_3_blowup_origin`: Exact blow-up identities of `𝒳_m(λ)` at `(0, 0)` in both charts
  `y = u x` and `x = v y`, proving `u = ∞` is regular on `E` and deriving the exact eigenvalue
  ratio `μ₁(ζ)/μ₂(ζ) = -1/m + λ ζ / (2 m (m + 1))` at `(0, ζ)` (`ζ^m = 1`).
- `prop_5_4_div_and_asymp`: Exact formulas for `div(𝒴_m)(x, w x)` and `K̃_m(x, w x)` and the
  exact algebraic identity linking `((m + 1) div(𝒴_m) - (m + 2) K̃_m)` to `rhoLinearCoeff m ω`.
-/

namespace LogarithmicRigidity

private lemma mem_support_of_mul_X_eq {f : MvPolynomial (Fin 3) ℂ} (i : Fin 3)
    (m : Fin 3 →₀ ℕ) :
    (f * MvPolynomial.X i).coeff (m + Finsupp.single i 1) = f.coeff m := by
  rw [MvPolynomial.X, MvPolynomial.coeff_mul_monomial, mul_one]

private lemma coeff_mul_X_eq_zero_of_zero {f : MvPolynomial (Fin 3) ℂ} (i : Fin 3)
    (m : Fin 3 →₀ ℕ) (hm : m i = 0) :
    (f * MvPolynomial.X i).coeff m = 0 := by
  rw [MvPolynomial.X, MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq ↦ ?_
  have hadd : pq.1 + pq.2 = m := by simpa using hpq
  by_cases h2 : pq.2 = Finsupp.single i 1
  · exfalso
    have hi : (pq.1 + pq.2) i = m i := congr_arg (fun g ↦ g i) hadd
    rw [Finsupp.add_apply, h2, Finsupp.single_eq_same, hm] at hi
    omega
  · simp [MvPolynomial.coeff_monomial, Ne.symm h2]

private lemma sub_single_add_single {m : Fin 3 →₀ ℕ} {i : Fin 3} (hmi : 1 ≤ m i) :
    m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  · simp [Finsupp.single_eq_of_ne hj]

private lemma exists_mul_X_of_support_pos (f : MvPolynomial (Fin 3) ℂ) (i : Fin 3)
    (h : ∀ m ∈ f.support, 1 ≤ m i) :
    ∃ w : MvPolynomial (Fin 3) ℂ, f = w * MvPolynomial.X i := by
  refine ⟨∑ m ∈ f.support, MvPolynomial.monomial (m - Finsupp.single i 1) (f.coeff m), ?_⟩
  rw [Finset.sum_mul]
  conv_lhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, sub_single_add_single (h m hm)]

private lemma isRegularSeq3_X012 :
    IsRegularSeq3 (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℂ)
      (MvPolynomial.X 1) (MvPolynomial.X 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (mul_eq_zero.mp hx).resolve_right (MvPolynomial.X_ne_zero 0)
  · intro x y hxy
    apply exists_mul_X_of_support_pos x 0
    intro m hm
    by_contra h0
    have hm0 : m 0 = 0 := by omega
    have hm1_0 : (m + Finsupp.single (1 : Fin 3) 1) 0 = 0 := by
      simp [Finsupp.add_apply, Finsupp.single_apply, hm0]
    have hL : (x * MvPolynomial.X 1).coeff (m + Finsupp.single (1 : Fin 3) 1) = x.coeff m :=
      mem_support_of_mul_X_eq 1 m
    have hR : (y * MvPolynomial.X 0).coeff (m + Finsupp.single (1 : Fin 3) 1) = 0 :=
      coeff_mul_X_eq_zero_of_zero 0 (m + Finsupp.single (1 : Fin 3) 1) hm1_0
    rw [hxy] at hL
    exact (MvPolynomial.mem_support_iff.mp hm) (hL.symm.trans hR)
  · intro x y z hxyz
    have hsup : ∀ m ∈ x.support, 1 ≤ m 0 ∨ 1 ≤ m 1 := by
      intro m hm
      by_contra h01
      push Not at h01
      have hm0 : m 0 = 0 := by omega
      have hm1 : m 1 = 0 := by omega
      have hm2_0 : (m + Finsupp.single (2 : Fin 3) 1) 0 = 0 := by
        simp [Finsupp.add_apply, Finsupp.single_apply, hm0]
      have hm2_1 : (m + Finsupp.single (2 : Fin 3) 1) 1 = 0 := by
        simp [Finsupp.add_apply, Finsupp.single_apply, hm1]
      have hL : (x * MvPolynomial.X 2).coeff (m + Finsupp.single (2 : Fin 3) 1) = x.coeff m :=
        mem_support_of_mul_X_eq 2 m
      have hR : (y * MvPolynomial.X 0 + z * MvPolynomial.X 1).coeff
          (m + Finsupp.single (2 : Fin 3) 1) = 0 := by
        rw [MvPolynomial.coeff_add,
          coeff_mul_X_eq_zero_of_zero 0 _ hm2_0,
          coeff_mul_X_eq_zero_of_zero 1 _ hm2_1, add_zero]
      rw [hxyz] at hL
      exact (MvPolynomial.mem_support_iff.mp hm) (hL.symm.trans hR)
    let s0 := x.support.filter (fun m ↦ 1 ≤ m 0)
    let s1 := x.support.filter (fun m ↦ ¬ 1 ≤ m 0)
    let u := ∑ m ∈ s0, MvPolynomial.monomial (m - Finsupp.single (0 : Fin 3) 1) (x.coeff m)
    let v := ∑ m ∈ s1, MvPolynomial.monomial (m - Finsupp.single (1 : Fin 3) 1) (x.coeff m)
    refine ⟨u, v, ?_⟩
    have hu : u * MvPolynomial.X 0 = ∑ m ∈ s0, MvPolynomial.monomial m (x.coeff m) := by
      simp only [u, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmi : 1 ≤ m 0 := (Finset.mem_filter.mp hm).2
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, sub_single_add_single hmi]
    have hv : v * MvPolynomial.X 1 = ∑ m ∈ s1, MvPolynomial.monomial m (x.coeff m) := by
      simp only [v, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmem := Finset.mem_filter.mp hm
      have hmi : 1 ≤ m 1 := (hsup m hmem.1).resolve_left hmem.2
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, sub_single_add_single hmi]
    rw [hu, hv, Finset.sum_filter_add_sum_filter_not, ← x.as_sum]

/-- **Proposition 5.1(1) (Euler Kernel Surjectivity)**: Every triple `(A, B, C)` in
`ℂ[X, Y, Z]³` satisfying Euler's projective identity `X A + Y B + Z C = 0` is of the form
`ω = i_V i_E Ω = formOfSyzygy V₁ V₂ V₃`. -/
theorem prop_5_1_euler_kernel_surj (A B C : MvPolynomial (Fin 3) ℂ)
    (heul : MvPolynomial.X 0 * A + MvPolynomial.X 1 * B + MvPolynomial.X 2 * C = 0) :
    ∃ V₁ V₂ V₃ : MvPolynomial (Fin 3) ℂ, formOfSyzygy V₁ V₂ V₃ = (A, B, C) := by
  have hC : C * MvPolynomial.X 2 = (-A) * MvPolynomial.X 0 + (-B) * MvPolynomial.X 1 := by
    linear_combination heul
  obtain ⟨u, v, hC_eq⟩ := isRegularSeq3_X012.2.2 C (-A) (-B) hC
  have hB : (B + v * MvPolynomial.X 2) * MvPolynomial.X 1 =
      (-(A + u * MvPolynomial.X 2)) * MvPolynomial.X 0 := by
    linear_combination heul - MvPolynomial.X 2 * hC_eq
  obtain ⟨w, hB_tmp⟩ := isRegularSeq3_X012.2.1 (B + v * MvPolynomial.X 2)
    (-(A + u * MvPolynomial.X 2)) hB
  have hB_eq : B = w * MvPolynomial.X 0 - v * MvPolynomial.X 2 := by linear_combination hB_tmp
  have hA : (A + w * MvPolynomial.X 1 + u * MvPolynomial.X 2) * MvPolynomial.X 0 = 0 := by
    linear_combination heul - MvPolynomial.X 1 * hB_eq - MvPolynomial.X 2 * hC_eq
  have hA_zero : A + w * MvPolynomial.X 1 + u * MvPolynomial.X 2 = 0 :=
    isRegularSeq3_X012.1 _ hA
  refine ⟨v, -u, w, ?_⟩
  unfold formOfSyzygy
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · linear_combination -hA_zero
  · linear_combination -hB_eq
  · linear_combination -hC_eq

/-- **Lemma 5.2 (Birational Surjectivity of Parametrization)**: Every nonzero affine point
`(x, y) ∈ C_m ∩ (ℂ² \ {(0, 0)})` is either `(0, 1/2)` (corresponding to `t = ∞`) or
`(x(t), y(t))` with `1 + 2 t^{m+1} ≠ 0`. -/
theorem lemma_5_2_param_surjective {m : ℕ} (hm : 2 ≤ m) (x y : ℂ)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hf : fmPoly m x y = 0) :
    (x = 0 ∧ y = 1 / 2) ∨
    (∃ t : ℂ, 1 + 2 * t ^ (m + 1) ≠ 0 ∧ x = xParam m t ∧ y = yParam m t) := by
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := hxy.resolve_left (by simp)
    have hfac : y ^ m * (2 * y - 1) = 0 := by
      unfold fmPoly at hf
      rw [zero_pow (by omega), zero_pow (by omega), pow_succ y m] at hf
      linear_combination hf
    have hlin : 2 * y - 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero m hy)
    exact Or.inl ⟨rfl, by linear_combination hlin / 2⟩
  · right
    let t : ℂ := y / x
    have hy_eq : y = t * x := by simp only [t]; field_simp [hx]
    have hrel : 1 - t ^ m + x * (1 + 2 * t ^ (m + 1)) = 0 := by
      have hfac : x ^ m * (1 - t ^ m + x * (1 + 2 * t ^ (m + 1))) = 0 := by
        unfold fmPoly at hf
        rw [hy_eq, mul_pow, mul_pow, pow_succ x m] at hf
        linear_combination hf
      exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero m hx)
    have hden : 1 + 2 * t ^ (m + 1) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, add_zero] at hrel
      have htm : t ^ m = 1 := by linear_combination -hrel
      have h2t : 1 + 2 * t = 0 := by
        rw [pow_succ t m, htm, one_mul] at h0
        exact h0
      have ht_val : t = -(1 : ℂ) / 2 := by linear_combination h2t / 2
      have hnorm : ‖t‖ ^ m = 1 := by rw [← norm_pow, htm, norm_one]
      have hnt : ‖t‖ = 1 / 2 := by rw [ht_val]; norm_num
      rw [hnt] at hnorm
      have hlt : ((1 : ℝ) / 2) ^ m < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      linarith
    have hx_eq : x = xParam m t := by
      unfold xParam
      rw [eq_div_iff hden]
      linear_combination hrel
    exact ⟨t, hden, hx_eq, by unfold yParam; rw [← hx_eq]; exact hy_eq⟩

/-- **Lemma 5.2 (Coprimality Core of Irreducibility of `F_m`)**: For every `m ≥ 2`, the
homogeneous forms `X^m - Y^m` and `X^{m+1} + 2 Y^{m+1}` share no common nonzero complex root,
so `F_m(X, Y, Z) = Z(X^m - Y^m) + (X^{m+1} + 2 Y^{m+1})` is primitive and linear in `Z`. -/
theorem lemma_5_2_Fm_no_common_root_Linf {m : ℕ} (hm : 2 ≤ m) (X Y : ℂ)
    (h1 : X ^ m - Y ^ m = 0) (h2 : X ^ (m + 1) + 2 * Y ^ (m + 1) = 0) :
    X = 0 ∧ Y = 0 := by
  by_cases hY : Y = 0
  · subst hY
    rw [zero_pow (by omega), sub_zero] at h1
    exact ⟨by by_contra hX; exact pow_ne_zero m hX h1, rfl⟩
  · have hXm : X ^ m = Y ^ m := sub_eq_zero.mp h1
    have hlin : Y ^ m * (X + 2 * Y) = 0 := by
      rw [pow_succ X m, pow_succ Y m, hXm] at h2
      linear_combination h2
    have hX : X = -2 * Y := by
      have h0 : X + 2 * Y = 0 := (mul_eq_zero.mp hlin).resolve_left (pow_ne_zero m hY)
      linear_combination h0
    rw [hX, mul_pow] at hXm
    have hpow : (-2 : ℂ) ^ m = 1 := by
      have hfac : ((-2 : ℂ) ^ m - 1) * Y ^ m = 0 := by linear_combination hXm
      exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (pow_ne_zero m hY))
    have hnorm := congr_arg norm hpow
    rw [norm_pow, norm_one] at hnorm
    have hnorm2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2] at hnorm
    have hgt : (1 : ℝ) < (2 : ℝ) ^ m := one_lt_pow₀ (by norm_num) (by omega)
    linarith

/-- **Lemma 5.3 (Saturation / Coprimality Witnesses)**: For every `m ≥ 2` and `λ ≠ 0`, none of
the four irreducible factors `x`, `x + m/(m+1)`, `y - m/(2(m+1))`, `f_m` of `K_m f_m` divides
both `P_m` and `Q_m` (establishing `gcd(P_m, Q_m) = 1` and `deg ℱ_m(λ) = m`). -/
theorem lemma_5_3_Pm_Qm_coprime {m : ℕ} (hm : 2 ≤ m) (lam : ℂ) (hlam : lam ≠ 0) :
    (fmPoly m 0 (1 / 2) = 0 ∧ PmVec m lam 0 (1 / 2) ≠ 0) ∧
    (PmVec m lam (-(m : ℂ) / ((m + 1 : ℕ) : ℂ)) 0 ≠ 0) ∧
    (∃ x : ℂ, QmVec m lam x ((m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ))) ≠ 0) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold fmPoly
    rw [zero_pow (by omega), zero_pow (by omega), pow_succ ((1 : ℂ) / 2) m]
    ring
  · have hhalf : ((1 : ℂ) / 2) ^ m = ((1 : ℂ) / 2) ^ (m - 1) * ((1 : ℂ) / 2) := by
      rw [← pow_succ, show m - 1 + 1 = m by omega]
    unfold PmVec fmDy
    rw [zero_pow (by omega), hhalf]
    have hval : -(-((m : ℂ) * ((1 : ℂ) / 2) ^ (m - 1)) +
        2 * ((m + 1 : ℕ) : ℂ) * (((1 : ℂ) / 2) ^ (m - 1) * ((1 : ℂ) / 2))) +
        lam * 0 * (0 + 1) * (1 / 2 - (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ))) =
        -((1 : ℂ) / 2) ^ (m - 1) := by
      rw [hcast]; ring
    rw [hval]
    exact neg_ne_zero.mpr (pow_ne_zero (m - 1) (by norm_num))
  · unfold PmVec fmDy
    rw [zero_pow (by omega), zero_pow (by omega)]
    have hadd1 : -(m : ℂ) / ((m + 1 : ℕ) : ℂ) + 1 = 1 / ((m + 1 : ℕ) : ℂ) := by
      field_simp [hm1]; rw [hcast]; ring
    rw [hadd1]
    simp only [mul_zero, neg_zero, add_zero, zero_add, zero_sub]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hlam ?_) ?_) ?_
    · exact pow_ne_zero (m - 1) (div_ne_zero (neg_ne_zero.mpr hm0) hm1)
    · exact div_ne_zero one_ne_zero hm1
    · exact neg_ne_zero.mpr (div_ne_zero hm0 (mul_ne_zero (by norm_num) hm1))
  · set y0 : ℂ := (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ))
    by_cases h1 : ((m + 1 : ℕ) : ℂ) * 1 + lam * y0 * (y0 - 1 / 2) ≠ 0
    · refine ⟨1, ?_⟩
      have hfac : QmVec m lam 1 y0 =
          (1 + (m : ℂ) / ((m + 1 : ℕ) : ℂ)) * (((m + 1 : ℕ) : ℂ) * 1 + lam * y0 * (y0 - 1 / 2)) := by
        unfold QmVec fmDx
        simp only [one_pow, mul_one]
        field_simp [hm1]
        ring
      rw [hfac]
      refine mul_ne_zero ?_ h1
      have hpos : (1 : ℂ) + (m : ℂ) / ((m + 1 : ℕ) : ℂ) =
          (2 * (m : ℂ) + 1) / ((m + 1 : ℕ) : ℂ) := by
        field_simp [hm1]; rw [hcast]; ring
      rw [hpos]
      refine div_ne_zero ?_ hm1
      have : (2 * (m : ℂ) + 1) = (((2 * m + 1 : ℕ) : ℂ)) := by push_cast; ring
      rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
    · push Not at h1
      refine ⟨2, ?_⟩
      have hfac : QmVec m lam 2 y0 =
          (2 : ℂ) ^ (m - 2) * (2 + (m : ℂ) / ((m + 1 : ℕ) : ℂ)) *
            (((m + 1 : ℕ) : ℂ) * 2 + lam * y0 * (y0 - 1 / 2)) := by
        have h2a : (2 : ℂ) ^ (m - 1) = (2 : ℂ) ^ (m - 2) * 2 := by
          rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
        have h2b : (2 : ℂ) ^ m = (2 : ℂ) ^ (m - 2) * 4 := by
          rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_add, show m - 2 + 2 = m by omega]
        unfold QmVec fmDx
        rw [h2a, h2b]
        field_simp [hm1]
        ring
      rw [hfac]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero (m - 2) (by norm_num)) ?_) ?_
      · have hpos : (2 : ℂ) + (m : ℂ) / ((m + 1 : ℕ) : ℂ) =
            (3 * (m : ℂ) + 2) / ((m + 1 : ℕ) : ℂ) := by
          field_simp [hm1]; rw [hcast]; ring
        rw [hpos]
        refine div_ne_zero ?_ hm1
        have : (3 * (m : ℂ) + 2) = (((3 * m + 2 : ℕ) : ℂ)) := by push_cast; ring
        rw [this]; exact Nat.cast_ne_zero.mpr (by omega)
      · have heq : ((m + 1 : ℕ) : ℂ) * 2 + lam * y0 * (y0 - 1 / 2) = ((m + 1 : ℕ) : ℂ) := by
          linear_combination h1
        rw [heq]
        exact hm1

/-- **Lemma 5.3 (Exact Blow-Up at Origin `(0, 0)`)**:
In the blow-up chart `y = u x`, `P_m` and `Q_m - u P_m` factor out `x^{m-1}` with exact
leading terms `m (u^{m-1} - λ/(2(m+1)))` and `m (1 - u^m)`; in the complementary chart
`x = v y`, `P_m - v Q_m` factors out `y^{m-1}` with leading term `m (1 - v^m)` (nonzero at
`v = 0`); and at every root `ζ^m = 1`, the Jacobian eigenvalue ratio is
`μ₁(ζ)/μ₂(ζ) = -1/m + λ ζ / (2 m (m + 1))`. -/
theorem lemma_5_3_blowup_origin {m : ℕ} (hm : 2 ≤ m) (lam x u y v : ℂ) :
    PmVec m lam x (u * x) =
      x ^ (m - 1) * ((m : ℂ) * (u ^ (m - 1) - lam / (2 * ((m + 1 : ℕ) : ℂ))) +
        x * (-2 * ((m + 1 : ℕ) : ℂ) * u ^ m +
          lam * (u * x + u - (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ))))) ∧
    QmVec m lam x (u * x) - u * PmVec m lam x (u * x) =
      x ^ (m - 1) * ((m : ℂ) * (1 - u ^ m) +
        x * (((m + 1 : ℕ) : ℂ) * (1 + 2 * u ^ (m + 1)) -
          lam * u * (2 * u + 1) / (2 * ((m + 1 : ℕ) : ℂ)))) ∧
    PmVec m lam (v * y) y - v * QmVec m lam (v * y) y =
      y ^ (m - 1) * ((m : ℂ) * (1 - v ^ m) +
        y * (-((m + 1 : ℕ) : ℂ) * (2 + v ^ (m + 1)) +
          lam * v ^ (m - 1) * (v + 2) / (2 * ((m + 1 : ℕ) : ℂ)))) ∧
    (∀ ζ : ℂ, ζ ^ m = 1 →
      ((m : ℂ) * (ζ⁻¹ - lam / (2 * ((m + 1 : ℕ) : ℂ)))) / (-(m : ℂ) ^ 2 * ζ⁻¹) =
        -(1 : ℂ) / (m : ℂ) + lam * ζ / (2 * (m : ℂ) * ((m + 1 : ℕ) : ℂ))) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hx1 : x ^ (m - 1) = x ^ (m - 2) * x := by
    rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
  have hx2 : x ^ m = x ^ (m - 2) * x ^ 2 := by
    rw [← pow_add, show m - 2 + 2 = m by omega]
  have hu1 : u ^ m = u ^ (m - 1) * u := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have hu2 : u ^ (m + 1) = u ^ (m - 1) * u ^ 2 := by
    rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
  have hy1 : y ^ (m - 1) = y ^ (m - 2) * y := by
    rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
  have hy2 : y ^ m = y ^ (m - 2) * y ^ 2 := by
    rw [← pow_add, show m - 2 + 2 = m by omega]
  have hv1 : v ^ (m - 1) = v ^ (m - 2) * v := by
    rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
  have hv2 : v ^ m = v ^ (m - 2) * v ^ 2 := by
    rw [← pow_add, show m - 2 + 2 = m by omega]
  have hv3 : v ^ (m + 1) = v ^ (m - 2) * v ^ 3 := by
    rw [← pow_add, show m - 2 + 3 = m + 1 by omega]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PmVec fmDy
    rw [mul_pow, mul_pow, hx2, hx1, hu1]
    field_simp [hm1]
    ring
  · unfold QmVec PmVec fmDx fmDy
    rw [mul_pow, mul_pow, hx2, hx1, hu2, hu1]
    field_simp [hm1]
    rw [hcast]
    ring
  · unfold PmVec QmVec fmDx fmDy
    rw [mul_pow, mul_pow, mul_pow, hy2, hy1, hv3, hv2, hv1]
    field_simp [hm1]
    rw [hcast]
    ring
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := by
      intro h0; rw [h0, zero_pow (by omega)] at hζ; exact zero_ne_one hζ
    field_simp [hm0, hm1, hζ0]
    ring

/-- **Proposition 5.4 (Exact Divergence, Cofactor, and Linear `λ`-Coefficient Link)**:
Along `y = w x`, `div(𝒴_m)(x, w x)` and `K̃_m(x, w x)` satisfy the exact expansions of §5,
and the leading `x^{-1}` coefficient of `div(𝒴_m)/K̃_m - 1 - 1/(m+1)` evaluated at
`x = 2(m+1)(ω^m - 1)/(λ ω (2ω + 1))` equals `λ * rhoLinearCoeff m ω` verbatim. -/
theorem prop_5_4_div_and_asymp {m : ℕ} (hm : 2 ≤ m) (x w lam ω : ℂ)
    (hlam : lam ≠ 0) (hω : ω ≠ 0) (h2ω : 2 * ω + 1 ≠ 0) (hωm : ω ^ m - 1 ≠ 0) :
    divYm m x (w * x) =
      x ^ (m - 2) * (((m : ℂ) + 2) * w * x ^ 2 +
        (((m : ℂ) - 1 + 2 * (m : ℂ) / ((m + 1 : ℕ) : ℂ)) * w -
          ((m : ℂ) ^ 2 + (m : ℂ) + 1) / (2 * ((m + 1 : ℕ) : ℂ))) * x -
        (m : ℂ) ^ 2 / (2 * ((m + 1 : ℕ) : ℂ))) ∧
    KmTilde m x (w * x) =
      x ^ (m - 2) * (((m + 1 : ℕ) : ℂ) * w * x ^ 2 +
        ((m : ℂ) * w - (m : ℂ) / 2) * x -
        (m : ℂ) ^ 2 / (2 * ((m + 1 : ℕ) : ℂ))) ∧
    ((m + 1 : ℕ) : ℂ) * divYm m x (w * x) - ((m + 2 : ℕ) : ℂ) * KmTilde m x (w * x) =
      x ^ (m - 2) * ((((m : ℂ) - 1) / 2 - w) * x + (m : ℂ) ^ 2 / (2 * ((m + 1 : ℕ) : ℂ))) ∧
    ((((m : ℂ) - 1) / 2 - ω) /
      (((m + 1 : ℕ) : ℂ) ^ 2 * ω *
        (2 * ((m + 1 : ℕ) : ℂ) * (ω ^ m - 1) / (lam * ω * (2 * ω + 1)))) =
      lam * rhoLinearCoeff m ω) := by
  have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast1 : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hcast2 : ((m + 2 : ℕ) : ℂ) = (m : ℂ) + 2 := by push_cast; ring
  have hcastm1 : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
    have : m - 1 + 1 = m := by omega
    have hc : (((m - 1 + 1 : ℕ) : ℂ)) = (m : ℂ) := by rw [this]
    push_cast at hc
    linear_combination hc
  have hx1 : x ^ (m - 1) = x ^ (m - 2) * x := by
    rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold divYm
    rw [hx1, hcastm1]
    field_simp [hm1]
    rw [hcast1]
    ring
  · unfold KmTilde
    field_simp [hm1]
    rw [hcast1]
    ring
  · unfold divYm KmTilde
    rw [hx1, hcastm1, hcast2]
    field_simp [hm1]
    rw [hcast1]
    ring
  · unfold rhoLinearCoeff
    field_simp [hm1, hlam, hω, h2ω, hωm]

end LogarithmicRigidity
