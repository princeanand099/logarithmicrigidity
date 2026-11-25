/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.CounterexampleCert

/-!
# Section 6 & Appendix A: Elimination, Hessians, `L_∞`, and Unconditional FTC Floquet Integrals

100% unconditional Mathlib-only proofs:
- `sing_Linf_empty`: `Sing(ℱ) ∩ L_∞ = ∅`
- `quartic_hessian_nodes`: Hessian determinants `192 ∓ 32i ≠ 0` at `(0, ±i)`
- `sing_PQ_elim`: exact integer elimination `vecP x y = 0 → vecQ x y = 0 → x = 0 ∨ q4Poly x = 0 ∨ q6Poly x = 0`
- `sing_PQ_x_zero`: exact `x = 0` stratum classification (`y = 0 ∨ y = I ∨ y = -I`)
- `floquet_integral_pos_oval1` & `floquet_integral_pos_oval2`: Fundamental Theorem of Calculus
  proof that any `C¹` periodic orbit of `(P, Q)` on either oval has `∫_0^T K(γ(t)) dt > 0`
  and `Real.exp (∫_0^T K(γ(t)) dt) > 1`.
-/

namespace LogarithmicRigidity

/-- **Proposition 6.2 (`L_∞`)**: `Sing(ℱ) ∩ L_∞ = ∅`. -/
theorem sing_Linf_empty (X Y : ℂ) (hXY : X ≠ 0 ∨ Y ≠ 0) :
    ¬ (48 * Y ^ 4 = 0 ∧ -(48 * X * Y ^ 3) = 0 ∧
      Y * (8 * X ^ 3 + 172 * X ^ 2 * Y + 48 * X * Y ^ 3 - 312 * Y ^ 3) -
      X * (320 * X ^ 3 + 16 * X ^ 2 * Y - 144 * X * Y ^ 2 + 48 * Y ^ 4) = 0) := by
  rintro ⟨hA, _, hC⟩
  have hY : Y = 0 := by
    have hY4 : Y ^ 4 = 0 := by
      have : (48 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hA).resolve_left this
    by_contra hne
    exact pow_ne_zero 4 hne hY4
  subst hY
  have hX : X ≠ 0 := hXY.resolve_right (by simp)
  have hX4 : -(320 : ℂ) * X ^ 4 = 0 := by
    linear_combination hC
  have h320 : -(320 : ℂ) ≠ 0 := by norm_num
  exact pow_ne_zero 4 hX ((mul_eq_zero.mp hX4).resolve_left h320)

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
  intro fxx fxy fyy
  have h1 : fxx 0 Complex.I * fyy 0 Complex.I - fxy 0 Complex.I ^ 2 = 192 - 32 * Complex.I := by
    simp only [fxx, fxy, fyy]
    linear_combination (-4 * Complex.I ^ 2 + 2 * Complex.I - 16) * 24 * Complex.I_sq +
      (24 * (-1) + 8) * (-4) * Complex.I_sq
  have h2 : fxx 0 (-Complex.I) * fyy 0 (-Complex.I) - fxy 0 (-Complex.I) ^ 2 =
      192 + 32 * Complex.I := by
    simp only [fxx, fxy, fyy]
    linear_combination (-4 * (-Complex.I) ^ 2 + 2 * (-Complex.I) - 16) * 24 * Complex.I_sq +
      (24 * (-1) + 8) * (-4) * Complex.I_sq
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1]; intro h0; have := congr_arg Complex.re h0; simp at this
  · rw [h2]; intro h0; have := congr_arg Complex.re h0; simp at this

/-- **Proposition 6.2 (`x = 0` Stratum)**: At `x = 0`, the affine singularities are
precisely `(0, 0)` and `(0, ±i)`. -/
theorem sing_PQ_x_zero (y : ℂ) (hP : vecP 0 y = 0) (hQ : vecQ 0 y = 0) :
    y = 0 ∨ y = Complex.I ∨ y = -Complex.I := by
  have hfac : -(312 : ℂ) * y * (y - Complex.I) * (y + Complex.I) = 0 := by
    simp only [vecP] at hP
    linear_combination hP + 312 * y * Complex.I_sq
  rcases mul_eq_zero.mp hfac with h1 | hNI
  · rcases mul_eq_zero.mp h1 with h2 | hI
    · have h312 : -(312 : ℂ) ≠ 0 := by norm_num
      exact Or.inl ((mul_eq_zero.mp h2).resolve_left h312)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hI))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hNI))

/-- **Proposition 6.2 (Elimination)**: Every complex affine singularity `(x, y)` of `(P, Q)`
satisfies `x = 0 ∨ q_4(x) = 0 ∨ q_6(x) = 0`. -/
theorem sing_PQ_elim (x y : ℂ) (hP : vecP x y = 0) (hQ : vecQ x y = 0) :
    x = 0 ∨ q4Poly x = 0 ∨ q6Poly x = 0 := by
  have hid : x * q4Poly x * q6Poly x =
      ((-44236800 : ℂ) * x ^ 7 * y + (-10879488 : ℂ) * x ^ 7 + (1105920 : ℂ) * x ^ 6 * y ^ 2 + (831594240 : ℂ) * x ^ 6 * y + (-27013440 : ℂ) * x ^ 6 + (-43711488 : ℂ) * x ^ 5 * y ^ 3 + (301824 : ℂ) * x ^ 5 * y ^ 2 + (-5464762560 : ℂ) * x ^ 5 * y + (1195688400 : ℂ) * x ^ 5 + (552874752 : ℂ) * x ^ 4 * y ^ 3 + (-131380416 : ℂ) * x ^ 4 * y ^ 2 + (13138317904 : ℂ) * x ^ 4 * y + (-7854778860 : ℂ) * x ^ 4 + (-2513487936 : ℂ) * x ^ 3 * y ^ 3 + (888004528 : ℂ) * x ^ 3 * y ^ 2 + (6929103304 : ℂ) * x ^ 3 * y + (15518836518 : ℂ) * x ^ 3 + (2784209568 : ℂ) * x ^ 2 * y ^ 3 + (-2327520968 : ℂ) * x ^ 2 * y ^ 2 + (-45123430802 : ℂ) * x ^ 2 * y + (12757761009 : ℂ) * x ^ 2 + (5960860488 : ℂ) * x * y ^ 3 + (-1159420644 : ℂ) * x * y ^ 2 + (9764888080 : ℂ) * x * y + (-31273783661 : ℂ) * x + (-7894696680 : ℂ) * y ^ 3 + (3990962820 : ℂ) * y ^ 2 + (25932547992 : ℂ) * y + (4174681732 : ℂ)) * vecP x y + ((44236800 : ℂ) * x ^ 8 + (-1105920 : ℂ) * x ^ 7 * y + (-831458304 : ℂ) * x ^ 7 + (43711488 : ℂ) * x ^ 6 * y ^ 2 + (10529280 : ℂ) * x ^ 6 * y + (6288739008 : ℂ) * x ^ 6 + (-836999424 : ℂ) * x ^ 5 * y ^ 2 + (134623488 : ℂ) * x ^ 5 * y + (-20214930608 : ℂ) * x ^ 5 + (6107173824 : ℂ) * x ^ 4 * y ^ 2 + (-2131467552 : ℂ) * x ^ 4 * y + (6233836252 : ℂ) * x ^ 4 + (-19121881152 : ℂ) * x ^ 3 * y ^ 2 + (10590478200 : ℂ) * x ^ 3 * y + (109597576986 : ℂ) * x ^ 3 + (12136501704 : ℂ) * x ^ 2 * y ^ 2 + (-17482431054 : ℂ) * x ^ 2 * y + (-119731674321 : ℂ) * x ^ 2 + (46640289852 : ℂ) * x * y ^ 2 + (-17326904478 : ℂ) * x * y + (-130306677384 : ℂ) * x + (-51315528420 : ℂ) * y ^ 2 + (34493846400 : ℂ) * y + (162812587548 : ℂ)) * vecQ x y := by
    simp only [vecP, vecQ, q4Poly, q6Poly]
    ring
  have h0 : x * q4Poly x * q6Poly x = 0 := by
    rw [hid, hP, hQ]
    ring
  rcases mul_eq_zero.mp h0 with h1 | h6
  · rcases mul_eq_zero.mp h1 with hx | h4
    · exact Or.inl hx
    · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h6)

/-- **Proposition 6.3 (Unconditional Floquet Integral via FTC on Oval 1)**:
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
  have hder : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (fun s ↦ g1Scaled (x s) (y s))
        (H1Scaled (x t) (y t) - 32000 * cofactorK (x t) (y t)) t := by
    intro t ht
    have hxt := hx t ht
    have hyt := hy t ht
    unfold g1Scaled H1Scaled
    convert
      ((((((((((hxt.pow 3).const_mul (-2713)).add
        (((hxt.pow 2).const_mul 678).mul hyt)).sub
        ((hxt.pow 2).const_mul 15081)).sub
        ((hxt.const_mul 18).mul (hyt.pow 2))).add
        ((hxt.const_mul 2399).mul hyt)).sub
        (hxt.const_mul 6176)).add
        ((hyt.pow 3).const_mul 111)).add
        ((hyt.pow 2).const_mul 2186)).add
        (hyt.const_mul 1537)) using 1
    simp only [Pi.pow_apply]
    ring
  have hint_diff : IntervalIntegrable
      (fun t ↦ H1Scaled (x t) (y t) - 32000 * cofactorK (x t) (y t)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    unfold H1Scaled cofactorK vecP vecQ
    fun_prop (disch := assumption)
  have hint_H1 : IntervalIntegrable (fun t ↦ H1Scaled (x t) (y t)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    unfold H1Scaled cofactorK vecP vecQ
    fun_prop (disch := assumption)
  have hint_K : IntervalIntegrable (fun t ↦ 32000 * cofactorK (x t) (y t)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    unfold cofactorK
    fun_prop (disch := assumption)
  have hftc : ∫ t in (0 : ℝ)..T, (H1Scaled (x t) (y t) - 32000 * cofactorK (x t) (y t)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint_diff, hper_x, hper_y, sub_self]
  have heq : 32000 * ∫ t in (0 : ℝ)..T, cofactorK (x t) (y t) =
      ∫ t in (0 : ℝ)..T, H1Scaled (x t) (y t) := by
    have hsub := intervalIntegral.integral_sub hint_H1 hint_K
    rw [hftc, intervalIntegral.integral_const_mul] at hsub
    linarith
  have hpos_H1 : 0 < ∫ t in (0 : ℝ)..T, H1Scaled (x t) (y t) := by
    apply intervalIntegral.integral_pos hT
    · unfold H1Scaled cofactorK vecP vecQ
      have hu : Set.Icc (0 : ℝ) T = Set.uIcc 0 T := (Set.uIcc_of_le (le_of_lt hT)).symm
      rw [hu]
      fun_prop (disch := assumption)
    · intro t ht
      exact le_of_lt (prop_6_3_and_theorem_1_4_part2.1 (x t) (y t)
        (hon t ⟨le_of_lt ht.1, ht.2⟩).1 (hon t ⟨le_of_lt ht.1, ht.2⟩).2)
    · refine ⟨0, ⟨le_rfl, le_of_lt hT⟩, ?_⟩
      exact prop_6_3_and_theorem_1_4_part2.1 (x 0) (y 0)
        (hon 0 ⟨le_rfl, le_of_lt hT⟩).1 (hon 0 ⟨le_rfl, le_of_lt hT⟩).2
  have hpos_K : 0 < ∫ t in (0 : ℝ)..T, cofactorK (x t) (y t) := by linarith
  exact ⟨hpos_K, Real.one_lt_exp_iff.mpr hpos_K⟩

/-- **Proposition 6.3 (Unconditional Floquet Integral via FTC on Oval 2)**:
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
  have hder : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (fun s ↦ g2Scaled (x s) (y s))
        (H2Scaled (x t) (y t) - 3200 * cofactorK (x t) (y t)) t := by
    intro t ht
    have hxt := hx t ht
    have hyt := hy t ht
    unfold g2Scaled H2Scaled
    convert
      ((((((hxt.pow 2).const_mul 762).add
        ((hxt.const_mul 77).mul hyt)).add
        (hxt.const_mul 879)).sub
        ((hyt.pow 2).const_mul 510)).sub
        (hyt.const_mul 142)) using 1
    ring
  have hint_diff : IntervalIntegrable
      (fun t ↦ H2Scaled (x t) (y t) - 3200 * cofactorK (x t) (y t)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    unfold H2Scaled cofactorK vecP vecQ
    fun_prop (disch := assumption)
  have hint_H2 : IntervalIntegrable (fun t ↦ H2Scaled (x t) (y t)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    unfold H2Scaled cofactorK vecP vecQ
    fun_prop (disch := assumption)
  have hint_K : IntervalIntegrable (fun t ↦ 3200 * cofactorK (x t) (y t)) MeasureTheory.volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    unfold cofactorK
    fun_prop (disch := assumption)
  have hftc : ∫ t in (0 : ℝ)..T, (H2Scaled (x t) (y t) - 3200 * cofactorK (x t) (y t)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint_diff, hper_x, hper_y, sub_self]
  have heq : 3200 * ∫ t in (0 : ℝ)..T, cofactorK (x t) (y t) =
      ∫ t in (0 : ℝ)..T, H2Scaled (x t) (y t) := by
    have hsub := intervalIntegral.integral_sub hint_H2 hint_K
    rw [hftc, intervalIntegral.integral_const_mul] at hsub
    linarith
  have hpos_H2 : 0 < ∫ t in (0 : ℝ)..T, H2Scaled (x t) (y t) := by
    apply intervalIntegral.integral_pos hT
    · unfold H2Scaled cofactorK vecP vecQ
      have hu : Set.Icc (0 : ℝ) T = Set.uIcc 0 T := (Set.uIcc_of_le (le_of_lt hT)).symm
      rw [hu]
      fun_prop (disch := assumption)
    · intro t ht
      exact le_of_lt (prop_6_3_and_theorem_1_4_part2.2.1 (x t) (y t)
        (hon t ⟨le_of_lt ht.1, ht.2⟩).1 (hon t ⟨le_of_lt ht.1, ht.2⟩).2)
    · refine ⟨0, ⟨le_rfl, le_of_lt hT⟩, ?_⟩
      exact prop_6_3_and_theorem_1_4_part2.2.1 (x 0) (y 0)
        (hon 0 ⟨le_rfl, le_of_lt hT⟩).1 (hon 0 ⟨le_rfl, le_of_lt hT⟩).2
  have hpos_K : 0 < ∫ t in (0 : ℝ)..T, cofactorK (x t) (y t) := by linarith
  exact ⟨hpos_K, Real.one_lt_exp_iff.mpr hpos_K⟩

end LogarithmicRigidity
