/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.CaseRNonZero
import LogarithmicRigidity.Section6ElimCert

/-!
# Section 6 (Unconditional Geometry, Compactness, and Saturation Certificates)

100% unconditional Mathlib-only proofs closing the Section 6 algebraic and topological gaps:
- `quartic_Linf_smooth`: `F_4(X, Y) = 2(X⁴ - X² Y² + Y⁴)` has no repeated complex roots
  (smoothness of the 2-nodal quartic (6.1) along `L_∞`).
- `quartic_real_pos_of_large` & `quartic_real_compact`: `C(ℝ) = {(x, y) ∈ ℝ² | f(x, y) = 0}`
  is compact (closed subset of the closed ball of radius `6`).
- `quartic_real_grad_ne_zero`: every real point on `f(x, y) = 0` is smooth (`∇f ≠ 0`).
- `counterexample_coprime_PQ`: no vertical line `x = x₀` lies in `{P = Q = 0}`, and
  `A(X, Y, 0) = 48 Y⁴ ≢ 0` (saturation / coprimality of `(P, Q)` in Proposition 6.2).
-/

namespace LogarithmicRigidity

/-- **Lemma 6.1 (`L_∞` Smoothness)**: The leading homogeneous part `F_4(X, Y) = 2(X⁴ - X² Y² + Y⁴)`
has no repeated nonzero complex roots, so `C` is smooth along `L_∞`. -/
theorem quartic_Linf_smooth (X Y : ℂ)
    (h0 : quarticF4 X Y = 0)
    (hdx : 4 * X * (2 * X ^ 2 - Y ^ 2) = 0)
    (hdy : 4 * Y * (2 * Y ^ 2 - X ^ 2) = 0) :
    X = 0 ∧ Y = 0 := by
  by_cases hX : X = 0
  · subst hX
    unfold quarticF4 at h0
    have hY4 : Y ^ 4 = 0 := by
      have h2 : (2 : ℂ) * Y ^ 4 = 0 := by linear_combination h0
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    exact ⟨rfl, by by_contra hY; exact pow_ne_zero 4 hY hY4⟩
  · by_cases hY : Y = 0
    · subst hY
      unfold quarticF4 at h0
      have hX4 : X ^ 4 = 0 := by
        have h2 : (2 : ℂ) * X ^ 4 = 0 := by linear_combination h0
        exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
      exact ⟨by by_contra h; exact pow_ne_zero 4 h hX4, rfl⟩
    · have h1 : 2 * X ^ 2 - Y ^ 2 = 0 :=
        (mul_eq_zero.mp hdx).resolve_left (mul_ne_zero (by norm_num) hX)
      have h2 : 2 * Y ^ 2 - X ^ 2 = 0 :=
        (mul_eq_zero.mp hdy).resolve_left (mul_ne_zero (by norm_num) hY)
      have h3 : (3 : ℂ) * X ^ 2 = 0 := by linear_combination 2 * h1 + h2
      have hX2 : X ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_left (by norm_num)
      exact absurd (by by_contra h; exact pow_ne_zero 2 h hX2) hX

/-- **Lemma 6.1 (Coercivity)**: For all `(x, y) ∈ ℝ²` with `x² + y² ≥ 30`, `f(x, y) > 0`. -/
theorem quartic_real_pos_of_large (x y : ℝ) (hr : 30 ≤ x ^ 2 + y ^ 2) :
    0 < quarticF x y := by
  have hid : quarticF x y =
      (1 / 10 : ℝ) * (x * (x + 5)) ^ 2 +
      (1 / 10 : ℝ) * (x ^ 2 + 5 * y) ^ 2 +
      (7 / 5 : ℝ) * (x ^ 2 - y ^ 2) ^ 2 +
      (1 / 5 : ℝ) * (y ^ 2) ^ 2 +
      (3 / 2 : ℝ) * y ^ 2 + 2 +
      ((2 / 5 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 - (21 / 2 : ℝ) * x ^ 2) := by
    unfold quarticF
    ring
  rw [hid]
  have h1 : 0 ≤ (x * (x + 5)) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (x ^ 2 + 5 * y) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (x ^ 2 - y ^ 2) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ (y ^ 2) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ y ^ 2 := sq_nonneg _
  have h6 : 0 ≤ x ^ 2 := sq_nonneg _
  nlinarith

/-- **Lemma 6.1 (Compactness)**: The real locus `C(ℝ) = {(x, y) ∈ ℝ² | f(x, y) = 0}` is compact. -/
theorem quartic_real_compact : IsCompact {p : ℝ × ℝ | quarticF p.1 p.2 = 0} := by
  have hclosed : IsClosed {p : ℝ × ℝ | quarticF p.1 p.2 = 0} := by
    have hcont : Continuous (fun p : ℝ × ℝ ↦ quarticF p.1 p.2) := by
      unfold quarticF
      fun_prop
    exact isClosed_eq hcont continuous_const
  have hsub : {p : ℝ × ℝ | quarticF p.1 p.2 = 0} ⊆ Metric.closedBall (0 : ℝ × ℝ) 6 := by
    intro p hp
    change quarticF p.1 p.2 = 0 at hp
    have hlt : p.1 ^ 2 + p.2 ^ 2 < 30 := by
      by_contra hge
      push Not at hge
      have hpos := quartic_real_pos_of_large p.1 p.2 hge
      linarith
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have hx2 : p.1 ^ 2 < 36 := by nlinarith [sq_nonneg p.2]
    have hy2 : p.2 ^ 2 < 36 := by nlinarith [sq_nonneg p.1]
    have hx : ‖p.1‖ ≤ 6 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by nlinarith, by nlinarith⟩
    have hy : ‖p.2‖ ≤ 6 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by nlinarith, by nlinarith⟩
    exact max_le hx hy
  exact (isCompact_closedBall (0 : ℝ × ℝ) 6).of_isClosed_subset hclosed hsub

/-- **Lemma 6.1 (Real Smoothness)**: Every real point `(x, y)` on `f(x, y) = 0` is smooth
(`∇f(x, y) ≠ 0`), and `f(-1, 0) < 0`, `f(1, 0) < 0`. -/
theorem quartic_real_smooth_and_sign :
    (∀ x y : ℝ, quarticF x y = 0 → quarticFx x y ≠ 0 ∨ quarticFy x y ≠ 0) ∧
    quarticF (-1 : ℝ) 0 < 0 ∧
    quarticF (1 : ℝ) 0 < 0 := by
  refine ⟨?_, by norm_num [quarticF], by norm_num [quarticF]⟩
  intro x y hf
  by_contra h
  push Not at h
  rcases h with ⟨hfx, hfy⟩
  have hfc : quarticF (x : ℂ) (y : ℂ) = 0 := by
    have : quarticF (x : ℂ) (y : ℂ) = ((quarticF x y : ℝ) : ℂ) := by
      unfold quarticF; push_cast; ring
    rw [this, hf]; simp
  have hfxc : quarticFx (x : ℂ) (y : ℂ) = 0 := by
    have : quarticFx (x : ℂ) (y : ℂ) = ((quarticFx x y : ℝ) : ℂ) := by
      unfold quarticFx; push_cast; ring
    rw [this, hfx]; simp
  have hfyc : quarticFy (x : ℂ) (y : ℂ) = 0 := by
    have : quarticFy (x : ℂ) (y : ℂ) = ((quarticFy x y : ℝ) : ℂ) := by
      unfold quarticFy; push_cast; ring
    rw [this, hfy]; simp
  have hsing := (lemma_6_1_quartic_geometry.2.1 (x : ℂ) (y : ℂ)).mp ⟨hfc, hfxc, hfyc⟩
  rcases hsing.2 with hyI | hyNI
  · have him := congr_arg Complex.im hyI
    simp at him
  · have him := congr_arg Complex.im hyNI
    simp at him

/-- **Proposition 6.2 (Saturation / Coprimality Certificate)**: No vertical line `x = x₀`
is contained in `{P = Q = 0}`, and `A(0, 1, 0) = 48 ≠ 0` so `Z ∤ A`. Together with
`sing_PQ_elim` (finitely many `x`-coordinates in `{P = Q = 0}`), this certifies
`gcd(P, Q) = 1` and `gcd(A, B, C) = 1` (hence `deg ℱ = 3`). -/
theorem counterexample_saturation_cert :
    (∀ x₀ : ℂ, ¬ (∀ y : ℂ, vecP x₀ y = 0 ∧ vecQ x₀ y = 0)) ∧
    (counterexampleLinfForm (0 : ℂ) 1).A ≠ 0 := by
  constructor
  · intro x₀ hall
    have hP0 := (hall 0).1
    have hP1 := (hall 1).1
    have hPm1 := (hall (-1)).1
    have hP2 := (hall 2).1
    have hQ0 := (hall 0).2
    have hdiff : 6 * (48 * x₀ - 312) = 0 := by
      simp only [vecP] at hP0 hP1 hPm1 hP2
      linear_combination hP2 - 3 * hP1 + 3 * hP0 - hPm1
    have hx : x₀ = 13 / 2 := by
      linear_combination hdiff / 288
    rw [hx] at hQ0
    simp only [vecQ] at hQ0
    norm_num at hQ0
  · simp only [counterexampleLinfForm, InducedOneForm.A]
    norm_num

end LogarithmicRigidity
