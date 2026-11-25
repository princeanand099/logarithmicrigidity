/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.Preliminaries
import LogarithmicRigidity.CaseRNonZero
import LogarithmicRigidity.Section6Q6Cert

/-!
# Small-Case and Non-Vacuity Sanity Checks

Concrete small-case evaluations and witness checks ensuring all definitions and
hypotheses are non-vacuous and free of `Nat` subtraction or division junk values.
-/

namespace LogarithmicRigidity

example : Hnodal 1 = 0 := by rfl
example : Hnodal 2 = 1 := by rfl
example : Hnodal 3 = 1 := by rfl
example : Hnodal 4 = 4 := by rfl
example : hBound 1 = 0 := by rfl
example : hBound 2 = 1 := by rfl
example : hBound 3 = 1 := by rfl
example : hBound 4 = 4 := by rfl
example : rNonZeroBound 1 = 0 := by rfl
example : rNonZeroBound 2 = 1 := by rfl
example : rNonZeroBound 3 = 2 := by rfl
example : rNonZeroBound 4 = 5 := by rfl

/-- Non-vacuity witness for `induced_one_form_euler`. -/
example : ∃ ω : InducedOneForm ℤ, ω.X * ω.A + ω.Y * ω.B + ω.Z * ω.C = 0 :=
  ⟨⟨1, 2, 3, 4, 5, 6⟩, induced_one_form_euler _⟩

/-- Concrete witness for `lemma_2_1_tau_ratio_criterion`: `μ₁ = 1, μ₂ = -1` gives `τ = 0 ∉ [4, ∞)`. -/
example : IsNonDicriticalTau (tauRatio ((1 : ℂ) + (-1)) ((1 : ℂ) * (-1))) := by
  rintro ⟨_, hre⟩
  unfold tauRatio at hre
  norm_num at hre

/-- Concrete witness for `prop_6_2_all_affine_singularities_nondicritical` at `(0, 0)`. -/
example : jacDet (0 : ℂ) 0 ≠ 0 ∧ IsNonDicriticalTau (tauRatio (jacTr 0 0) (jacDet 0 0)) :=
  prop_6_2_all_affine_singularities_nondicritical 0 0
    (by unfold vecP; norm_num) (by unfold vecQ; norm_num)

/-- Concrete witness for `lemma_6_1_quartic_geometry` at `(0, i)`. -/
example : quarticF (0 : ℂ) Complex.I = 0 ∧ quarticFx (0 : ℂ) Complex.I = 0 ∧
    quarticFy (0 : ℂ) Complex.I = 0 :=
  (lemma_6_1_quartic_geometry.2.1 0 Complex.I).mpr ⟨rfl, Or.inl rfl⟩

end LogarithmicRigidity
