/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs

/-!
# Section 2: Preliminaries, Projective 1-Forms, Lemma 2.1, and Lemma 2.4

Covers:
- Induced homogeneous 1-form Euler identity (Eq. 2.1)
- Algebraic non-dicriticality criterion (Lemma 2.1)
- Monotonicity and superadditivity of the Harnack oval bound `h` (Lemma 2.4)
-/

namespace LogarithmicRigidity

/-- Euler's projective condition `X·A + Y·B + Z·C = 0` holds identically for (2.1). -/
theorem induced_one_form_euler {R : Type*} [CommRing R] (ω : InducedOneForm R) :
    ω.X * ω.A + ω.Y * ω.B + ω.Z * ω.C = 0 := by
  simp only [InducedOneForm.A, InducedOneForm.B, InducedOneForm.C]
  ring

/-- **Lemma 2.1**: Algebraic non-dicriticality criterion `τ = ρ + ρ⁻¹ + 2 ∉ [4, ∞) → ρ ∉ ℚ_{>0}`. -/
theorem lemma_2_1_tau_ratio_criterion (μ₁ μ₂ : ℂ) (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0) :
    let ρ := μ₁ / μ₂
    let τ := tauRatio (μ₁ + μ₂) (μ₁ * μ₂)
    τ = ρ + ρ⁻¹ + 2 ∧
    (InRealRayFour τ ↔ ρ.im = 0 ∧ 0 < ρ.re) ∧
    (IsNonDicriticalTau τ → ∀ q : ℚ, 0 < q → ρ ≠ (q : ℂ)) := by
  intro ρ τ
  have hτ : τ = ρ + ρ⁻¹ + 2 := by
    simp only [τ, ρ, tauRatio]
    rw [inv_div]
    field_simp [hμ₁, hμ₂]
    ring
  have hρ : ρ ≠ 0 := div_ne_zero hμ₁ hμ₂
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρ
  have hns_ne : Complex.normSq ρ ≠ 0 := ne_of_gt hns
  have h2im : (2 : ℂ).im = 0 := by simp
  have h2re : (2 : ℂ).re = 2 := by simp
  have hray : InRealRayFour τ ↔ ρ.im = 0 ∧ 0 < ρ.re := by
    constructor
    · rintro ⟨him, hre⟩
      rw [hτ] at him hre
      simp only [Complex.add_im, Complex.inv_im, h2im, add_zero] at him
      simp only [Complex.add_re, Complex.inv_re, h2re] at hre
      have him_mul := congr_arg (· * Complex.normSq ρ) him
      rw [add_mul, zero_mul, div_mul_cancel₀ _ hns_ne] at him_mul
      have him' : ρ.im * (Complex.normSq ρ - 1) = 0 := by
        calc ρ.im * (Complex.normSq ρ - 1)
            = ρ.im * Complex.normSq ρ + -ρ.im := by ring
          _ = 0 := him_mul
      have hρim : ρ.im = 0 := by
        rcases mul_eq_zero.mp him' with h | h
        · exact h
        · have hns1 : Complex.normSq ρ = 1 := by linarith
          rw [hns1, div_one] at hre
          have hsq : Complex.normSq ρ = ρ.re * ρ.re + ρ.im * ρ.im := Complex.normSq_apply ρ
          have him2 : ρ.im * ρ.im = 0 := by nlinarith [sq_nonneg ρ.im, sq_nonneg (ρ.re - 1)]
          exact mul_self_eq_zero.mp him2
      refine ⟨hρim, ?_⟩
      have hmul : 4 * Complex.normSq ρ ≤
          (ρ.re + ρ.re / Complex.normSq ρ + 2) * Complex.normSq ρ :=
        mul_le_mul_of_nonneg_right hre (le_of_lt hns)
      rw [add_mul, add_mul, div_mul_cancel₀ _ hns_ne] at hmul
      have hns_re : Complex.normSq ρ = ρ.re * ρ.re := by
        rw [Complex.normSq_apply, hρim]
        ring
      rw [hns_re] at hmul
      have hid : ρ.re * ((ρ.re - 1) * (ρ.re - 1)) =
          ρ.re * (ρ.re * ρ.re) + ρ.re + 2 * (ρ.re * ρ.re) - 4 * (ρ.re * ρ.re) := by ring
      have hfact : 0 ≤ ρ.re * ((ρ.re - 1) * (ρ.re - 1)) := by linarith
      by_contra hle
      push Not at hle
      have hne0 : ρ.re ≠ 0 := by
        intro h0
        rw [h0] at hns_re
        linarith
      have hlt : ρ.re < 0 := lt_of_le_of_ne hle hne0
      have hpos : 0 < (ρ.re - 1) * (ρ.re - 1) := by nlinarith
      have hneg : ρ.re * ((ρ.re - 1) * (ρ.re - 1)) < 0 := mul_neg_of_neg_of_pos hlt hpos
      linarith
    · rintro ⟨hρim, hρre⟩
      refine ⟨?_, ?_⟩
      · rw [hτ]
        simp only [Complex.add_im, Complex.inv_im, h2im, hρim, neg_zero, zero_div, add_zero]
      · rw [hτ]
        simp only [Complex.add_re, Complex.inv_re, h2re]
        have hns_re : Complex.normSq ρ = ρ.re * ρ.re := by
          rw [Complex.normSq_apply, hρim]
          ring
        rw [hns_re]
        have hρre_ne : ρ.re ≠ 0 := ne_of_gt hρre
        have hdiff : ρ.re + ρ.re / (ρ.re * ρ.re) + 2 - 4 = (ρ.re - 1) ^ 2 / ρ.re := by
          field_simp [hρre_ne]
          ring
        have hnn : 0 ≤ (ρ.re - 1) ^ 2 / ρ.re :=
          div_nonneg (sq_nonneg _) (le_of_lt hρre)
        linarith
  refine ⟨hτ, hray, ?_⟩
  intro hnd q hq hEq
  apply hnd
  rw [hray]
  rw [hEq]
  exact ⟨by simp, by simp [hq]⟩

private lemma two_dvd_mul_pred (n : ℕ) : 2 ∣ n * (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel]
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨(k + k + 1) * k, by ring⟩
    · exact ⟨(k + 1) * (2 * k + 1), by ring⟩

private lemma aVal_le_one (m : ℕ) : aVal m ≤ 1 := by
  simp only [aVal]
  split_ifs <;> omega

private lemma hBound_two_mul (d : ℕ) (hd : 1 ≤ d) :
    2 * hBound d = (d - 1) * (d - 2) + 2 * aVal d := by
  cases d with
  | zero => omega
  | succ n =>
    simp only [hBound]
    have hmul : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.mul_div_cancel' (two_dvd_mul_pred n)
    have hsub1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
    have hsub2 : n + 1 - 2 = n - 1 := by omega
    rw [hsub1, hsub2]
    omega

/-- **Lemma 2.4**: Monotonicity and superadditivity of the Harnack oval bound `h`. -/
theorem lemma_2_4_hBound_mono_superadd :
    (∀ d : ℕ, hBound d ≤ hBound (d + 1)) ∧
    (∀ a b : ℕ, hBound a + hBound b ≤ hBound (a + b)) ∧
    (∀ l : List ℕ, (l.map hBound).sum ≤ hBound l.sum) := by
  have hstep : ∀ d : ℕ, hBound d ≤ hBound (d + 1) := by
    intro d
    match d with
    | 0 => simp [hBound]
    | 1 => simp [hBound, aVal]
    | n + 2 =>
      have h1 := hBound_two_mul (n + 2) (by omega)
      have h2 := hBound_two_mul (n + 3) (by omega)
      have ha1 := aVal_le_one (n + 2)
      have hs1 : n + 2 - 1 = n + 1 := by omega
      have hs2 : n + 2 - 2 = n := by omega
      have hs3 : n + 3 - 1 = n + 2 := by omega
      have hs4 : n + 3 - 2 = n + 1 := by omega
      rw [hs1, hs2] at h1
      rw [hs3, hs4] at h2
      nlinarith
  have hsuper : ∀ a b : ℕ, hBound a + hBound b ≤ hBound (a + b) := by
    intro a b
    match a, b with
    | 0, b => simp [hBound]
    | a, 0 => simp [hBound]
    | 1, b =>
      have h1 : hBound 1 = 0 := by simp [hBound, aVal]
      rw [h1, zero_add, Nat.add_comm]
      exact hstep b
    | a, 1 =>
      have h1 : hBound 1 = 0 := by simp [hBound, aVal]
      rw [h1, add_zero]
      exact hstep a
    | m + 2, n + 2 =>
      have h1 := hBound_two_mul (m + 2) (by omega)
      have h2 := hBound_two_mul (n + 2) (by omega)
      have h3 := hBound_two_mul (m + 2 + (n + 2)) (by omega)
      have ha1 := aVal_le_one (m + 2)
      have ha2 := aVal_le_one (n + 2)
      have hm1 : m + 2 - 1 = m + 1 := by omega
      have hm2 : m + 2 - 2 = m := by omega
      have hn1 : n + 2 - 1 = n + 1 := by omega
      have hn2 : n + 2 - 2 = n := by omega
      have hs1 : m + 2 + (n + 2) - 1 = m + n + 3 := by omega
      have hs2 : m + 2 + (n + 2) - 2 = m + n + 2 := by omega
      rw [hm1, hm2] at h1
      rw [hn1, hn2] at h2
      rw [hs1, hs2] at h3
      nlinarith
  refine ⟨hstep, hsuper, ?_⟩
  intro l
  induction l with
  | nil => simp [hBound]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact le_trans (Nat.add_le_add_left ih (hBound x)) (hsuper x xs.sum)

/-- `hBound m = Hnodal m` for all `m ≥ 1`. -/
theorem hBound_eq_Hnodal {m : ℕ} (hm : 1 ≤ m) : hBound m = Hnodal m := by
  cases m with
  | zero => omega
  | succ n => rfl

/-- Monotonicity `a ≤ b → hBound a ≤ hBound b`. -/
theorem hBound_mono {a b : ℕ} (h : a ≤ b) : hBound a ≤ hBound b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact le_rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (lemma_2_4_hBound_mono_superadd.1 n)

end LogarithmicRigidity
