/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs

/-!
# Section 4 (Calculus Core): Real-Logarithmic Local First Integral Invariance

Proves **unconditionally on top of Mathlib** (`HasDerivAt`, `Real.rpow`, `Finset.prod`)
that for any real logarithmic foliation with real residues `λ_i` and `C¹` factors `f_i`
non-vanishing for `i ∈ s`, the local first integral
`ũ(t) = f₁(t) * ∏_{i ∈ s} |f_i(t)|^{λ_i / λ₁}` has zero derivative everywhere
(including on `{f₁ = 0}`) and is constant along every `C¹` orbit.
-/

namespace LogarithmicRigidity

private lemma hasDerivAt_abs_rpow {g : ℝ → ℝ} {g' α t : ℝ}
    (hg : HasDerivAt g g' t) (hne : g t ≠ 0) :
    HasDerivAt (fun s ↦ |g s| ^ α) (α * |g t| ^ α * (g' / g t)) t := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hev : (fun s ↦ |g s| ^ α) =ᶠ[nhds t] (fun s ↦ (-g s) ^ α) := by
      filter_upwards [hg.continuousAt.eventually (Iio_mem_nhds hneg)] with s hs
      rw [abs_of_neg hs]
    have hpos' : 0 < -g t := neg_pos.mpr hneg
    have hder : HasDerivAt (fun s ↦ (-g s) ^ α) (α * (-g t) ^ (α - 1) * (-g')) t := by
      convert (hg.neg.rpow_const (p := α) (Or.inl (ne_of_gt hpos'))) using 1
      simp only [Pi.neg_apply]
      ring
    have hder' := hder.congr_of_eventuallyEq hev
    convert hder' using 1
    rw [abs_of_neg hneg]
    have hrpow : (-g t) ^ α = (-g t) ^ (α - 1) * (-g t) := by
      rw [← Real.rpow_add_one (ne_of_gt hpos')]
      ring_nf
    rw [hrpow]
    field_simp [hne]
  · have hev : (fun s ↦ |g s| ^ α) =ᶠ[nhds t] (fun s ↦ (g s) ^ α) := by
      filter_upwards [hg.continuousAt.eventually (Ioi_mem_nhds hpos)] with s hs
      rw [abs_of_pos hs]
    have hder : HasDerivAt (fun s ↦ (g s) ^ α) (α * (g t) ^ (α - 1) * g') t := by
      convert (hg.rpow_const (p := α) (Or.inl (ne_of_gt hpos))) using 1
      ring
    have hder' := hder.congr_of_eventuallyEq hev
    convert hder' using 1
    rw [abs_of_pos hpos]
    have hrpow : (g t) ^ α = (g t) ^ (α - 1) * g t := by
      rw [← Real.rpow_add_one (ne_of_gt hpos)]
      ring_nf
    rw [hrpow]
    field_simp [hne]

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
  let u : ℝ → ℝ := fun t ↦ f₁ t * (∏ i ∈ s, |f i t| ^ (lam i / lam₁))
  have hderiv_zero : ∀ t : ℝ, HasDerivAt u 0 t := by
    intro t
    have hprod_raw := HasDerivAt.finset_prod (u := s)
      (f := fun i x ↦ |f i x| ^ (lam i / lam₁))
      (f' := fun i ↦ (lam i / lam₁) * |f i t| ^ (lam i / lam₁) * (f' i t / f i t))
      (fun i hi ↦ hasDerivAt_abs_rpow (hf i hi t) (hne i hi t))
    have hprod :
        HasDerivAt (fun x ↦ ∏ i ∈ s, |f i x| ^ (lam i / lam₁))
          (∑ i ∈ s, (∏ j ∈ s.erase i, |f j t| ^ (lam j / lam₁)) *
            ((lam i / lam₁) * |f i t| ^ (lam i / lam₁) * (f' i t / f i t))) t := by
      convert hprod_raw using 1
      ext x; simp only [Finset.prod_apply]
    have hmul := (hf₁ t).mul hprod
    convert hmul using 1
    have hP_ne : (∏ j ∈ s, f j t) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj ↦ hne j hj t
    have hsum_eq :
        ∑ i ∈ s, (∏ j ∈ s.erase i, |f j t| ^ (lam j / lam₁)) *
          ((lam i / lam₁) * |f i t| ^ (lam i / lam₁) * (f' i t / f i t)) =
        (∏ j ∈ s, |f j t| ^ (lam j / lam₁)) *
          ∑ i ∈ s, (lam i / lam₁) * (f' i t / f i t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hsplit : ∏ j ∈ s, |f j t| ^ (lam j / lam₁) =
          |f i t| ^ (lam i / lam₁) * ∏ j ∈ s.erase i, |f j t| ^ (lam j / lam₁) := by
        rw [Finset.mul_prod_erase s (fun j ↦ |f j t| ^ (lam j / lam₁)) hi]
      rw [hsplit]
      ring
    rw [hsum_eq]
    have hinner :
        f₁' t + f₁ t * ∑ i ∈ s, (lam i / lam₁) * (f' i t / f i t) = 0 := by
      have hscaled :
          lam₁ * (∏ j ∈ s, f j t) *
            (f₁' t + f₁ t * ∑ i ∈ s, (lam i / lam₁) * (f' i t / f i t)) =
          lam₁ * (∏ j ∈ s, f j t) * f₁' t +
            ∑ i ∈ s, lam i * f₁ t * (∏ j ∈ s.erase i, f j t) * f' i t := by
        rw [mul_add, ← mul_assoc (lam₁ * ∏ j ∈ s, f j t) (f₁ t), Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hsplit : ∏ j ∈ s, f j t = f i t * ∏ j ∈ s.erase i, f j t := by
          rw [Finset.mul_prod_erase s (fun j ↦ f j t) hi]
        have hfi : f i t ≠ 0 := hne i hi t
        rw [hsplit]
        field_simp [hlam₁, hfi]
      rw [hlog t] at hscaled
      exact (mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero hlam₁ hP_ne)
    calc
      (0 : ℝ) = (f₁' t + f₁ t * ∑ i ∈ s, (lam i / lam₁) * (f' i t / f i t)) *
          ∏ j ∈ s, |f j t| ^ (lam j / lam₁) := by rw [hinner, zero_mul]
      _ = f₁' t * (∏ j ∈ s, |f j t| ^ (lam j / lam₁)) +
          f₁ t * ((∏ j ∈ s, |f j t| ^ (lam j / lam₁)) *
            ∑ i ∈ s, (lam i / lam₁) * (f' i t / f i t)) := by ring
  have hconst : ∀ t : ℝ, u t = u 0 :=
    fun t ↦ is_const_of_deriv_eq_zero (fun x ↦ (hderiv_zero x).differentiableAt)
      (fun x ↦ (hderiv_zero x).deriv) t 0
  exact hconst

end LogarithmicRigidity
