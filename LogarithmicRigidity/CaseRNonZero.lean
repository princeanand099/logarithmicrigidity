/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.Preliminaries

/-!
# Section 6 (Part A): Arithmetic Bounds and 2-Nodal Quartic Geometry

100% unconditional Mathlib-only proofs:
- Pure arithmetic inequalities for Theorem 1.4(1) (`hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound`)
- Lemma 6.1 (geometry, exact complex singular locus `{(0, ±i)}` via Nullstellensatz, compactness, IVT)
-/

namespace LogarithmicRigidity

private lemma aVal_le_one (n : ℕ) : aVal n ≤ 1 := by
  unfold aVal
  split_ifs <;> omega

private lemma two_dvd_mul_pred (n : ℕ) : 2 ∣ n * (n - 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k * (n - 1), ?_⟩
    rw [hk]
    ring
  · refine ⟨n * k, ?_⟩
    have hsub : n - 1 = 2 * k := by omega
    rw [hsub]
    ring

private lemma two_mul_tri_div_two (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.mul_div_cancel' (two_dvd_mul_pred n)

/-- Pure arithmetic bound `h(m) ≤ rNonZeroBound(m)` for all `m ≥ 1`. -/
theorem hBound_le_rNonZeroBound {m : ℕ} (hm : 1 ≤ m) :
    hBound m ≤ rNonZeroBound m := by
  match m with
  | 0 => omega
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 =>
    simp only [hBound, rNonZeroBound]
    have hdiv1 := two_mul_tri_div_two (k + 4)
    have hdiv2 := two_mul_tri_div_two (k + 3)
    have ha1 := aVal_le_one (k + 4)
    have hsub1 : k + 4 - 1 = k + 3 := by omega
    have hsub2 : k + 4 - 2 = k + 2 := by omega
    have hsub3 : k + 3 - 1 = k + 2 := by omega
    rw [hsub1, hsub2] at *
    rw [hsub3] at hdiv2
    have hring : (k + 4) * (k + 3) = (k + 3) * (k + 2) + 2 * (k + 3) := by ring
    omega

/-- Pure arithmetic bound `h(a) + h(b) ≤ rNonZeroBound(m)` for all `m ≥ 1`, `a, b ≥ 1`, `a + b = m + 1`. -/
theorem hBound_add_le_rNonZeroBound {m a b : ℕ} (hm : 1 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a + b = m + 1) : hBound a + hBound b ≤ rNonZeroBound m := by
  by_cases ha1 : a = 1
  · subst ha1
    have hbm : b = m := by omega
    subst hbm
    simpa [hBound, aVal] using hBound_le_rNonZeroBound hm
  · by_cases hb1 : b = 1
    · subst hb1
      have ham : a = m := by omega
      subst ham
      simpa [hBound, aVal] using hBound_le_rNonZeroBound hm
    · by_cases hm3 : m = 3
      · subst hm3
        have haeq : a = 2 := by omega
        have hbeq : b = 2 := by omega
        subst haeq
        subst hbeq
        decide
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
        simp only [hBound, rNonZeroBound]
        have hdivM := two_mul_tri_div_two (k + 4)
        have hdivA := two_mul_tri_div_two (a' + 1)
        have hdivB := two_mul_tri_div_two (b' + 1)
        have haA := aVal_le_one (a' + 2)
        have haB := aVal_le_one (b' + 2)
        have hkm1 : k + 4 = a' + b' + 3 := by omega
        have hkm2 : k + 3 = a' + b' + 2 := by omega
        have hsubM : k + 4 - 1 = k + 3 := by omega
        have hsubA1 : a' + 2 - 1 = a' + 1 := by omega
        have hsubA2 : a' + 2 - 2 = a' := by omega
        have hsubA3 : a' + 1 - 1 = a' := by omega
        have hsubB1 : b' + 2 - 1 = b' + 1 := by omega
        have hsubB2 : b' + 2 - 2 = b' := by omega
        have hsubB3 : b' + 1 - 1 = b' := by omega
        rw [hsubM, hsubA1, hsubA2, hsubB1, hsubB2] at *
        rw [hsubA3] at hdivA
        rw [hsubB3] at hdivB
        have hring : (k + 4) * (k + 3) =
            (a' + 1) * a' + (b' + 1) * b' + 2 * (a' * b' + 2 * a' + 2 * b' + 3) := by
          rw [hkm1, hkm2]
          ring
        omega

/-- **Lemma 6.1**: Geometry of the 2-nodal quartic `f(x, y) = 0` (6.1). -/
theorem lemma_6_1_quartic_geometry :
    (∀ X Y : ℝ, (X ≠ 0 ∨ Y ≠ 0) → 0 < quarticF4 X Y) ∧
    (∀ x y : ℂ, quarticF x y = 0 ∧ quarticFx x y = 0 ∧ quarticFy x y = 0 ↔
      x = 0 ∧ (y = Complex.I ∨ y = -Complex.I)) ∧
    (∀ y : ℝ, 0 < quarticF (0 : ℝ) y) ∧
    quarticF (-(1 : ℝ) / 2) 0 = 0 ∧
    (∃ ystar : ℝ, 0 < ystar ∧ ystar < 1 ∧ quarticF 1 ystar = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y hXY
    unfold quarticF4
    rcases hXY with hX | hY
    · have hX2 : 0 < X ^ 2 := sq_pos_of_ne_zero hX
      have hX4 : 0 < X ^ 4 := by nlinarith
      nlinarith [sq_nonneg (Y ^ 2 - X ^ 2 / 2)]
    · have hY2 : 0 < Y ^ 2 := sq_pos_of_ne_zero hY
      have hY4 : 0 < Y ^ 4 := by nlinarith
      nlinarith [sq_nonneg (X ^ 2 - Y ^ 2 / 2)]
  · intro x y
    constructor
    · rintro ⟨hf, hfx, hfy⟩
      simp only [quarticF, quarticFx, quarticFy] at hf hfx hfy
      have hx : x = 0 := by
        by_contra hne
        have hfx_fac : x * (8 * x ^ 2 + 3 * x - 4 * y ^ 2 + 2 * y - 16) = 0 := by
          linear_combination hfx
        have hg : 8 * x ^ 2 + 3 * x - 4 * y ^ 2 + 2 * y - 16 = 0 :=
          (mul_eq_zero.mp hfx_fac).resolve_left hne
        have hzero : (3366807857231104 : ℂ) = 0 := by
          linear_combination
            (-39064264535040 * x * y ^ 2 - 16326528147840 * x * y - 205853122468832 * x +
              234982602309120 * y ^ 3 - 21635306185344 * y ^ 2 - 187925239499584 * y -
              582245684222848) * hf +
            (9766066133760 * x ^ 3 * y ^ 2 + 4081632036960 * x ^ 3 * y +
              51463280617208 * x ^ 3 - 58745650577280 * x ^ 2 * y ^ 3 +
              6629584813056 * x ^ 2 * y ^ 2 + 47491513879516 * x ^ 2 * y +
              151994331132863 * x ^ 2 - 8163264073920 * x * y ^ 3 -
              14275676555584 * x * y ^ 2 - 30297136035264 * x * y - 78832803109504 * x -
              8977102918400 * y ^ 4 + 124651896593016 * y ^ 3 - 19198883666624 * y ^ 2 +
              79154493116920 * y - 283206201604800) * hg +
            (9766066133760 * x * y ^ 3 + 59498738086056 * x * y - 66487374175037 * x -
              58745650577280 * y ^ 4 + 920275087136 * y ^ 3 + 52805883323724 * y ^ 2 +
              96742177242882 * y + 276091846509936) * hfy
        norm_num at hzero
      subst hx
      have h1 : (y ^ 2 + 1) ^ 2 = 0 := by
        linear_combination hf / 2
      have h2 : y ^ 2 + 1 = 0 := sq_eq_zero_iff.mp h1
      have hy2 : (y - Complex.I) * (y + Complex.I) = 0 := by
        linear_combination h2 - Complex.I_sq
      rcases mul_eq_zero.mp hy2 with hyI | hyNI
      · exact ⟨rfl, Or.inl (sub_eq_zero.mp hyI)⟩
      · exact ⟨rfl, Or.inr (eq_neg_of_add_eq_zero_left hyNI)⟩
    · rintro ⟨rfl, rfl | rfl⟩
      · refine ⟨?_, ?_, ?_⟩
        · simp only [quarticF]
          linear_combination 2 * (Complex.I ^ 2 + 1) * Complex.I_sq
        · simp only [quarticFx]
          ring
        · simp only [quarticFy]
          linear_combination 8 * Complex.I * Complex.I_sq
      · refine ⟨?_, ?_, ?_⟩
        · simp only [quarticF]
          linear_combination 2 * (Complex.I ^ 2 + 1) * Complex.I_sq
        · simp only [quarticFx]
          ring
        · simp only [quarticFy]
          linear_combination -8 * Complex.I * Complex.I_sq
  · intro y
    have hEq : quarticF (0 : ℝ) y = 2 * (y ^ 2 + 1) ^ 2 := by
      unfold quarticF
      ring
    rw [hEq]
    positivity
  · norm_num [quarticF]
  · have hcont : ContinuousOn (fun y : ℝ ↦ quarticF (1 : ℝ) y) (Set.Icc 0 1) := by
      unfold quarticF
      fun_prop
    have hmem : (0 : ℝ) ∈ Set.Ioo (quarticF (1 : ℝ) 0) (quarticF (1 : ℝ) 1) := by
      norm_num [quarticF]
    rcases intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont hmem with
      ⟨ystar, ⟨h0, h1⟩, hy⟩
    exact ⟨ystar, h0, h1, hy⟩

end LogarithmicRigidity
