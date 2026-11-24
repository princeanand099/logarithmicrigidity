/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.Preliminaries
import LogarithmicRigidity.LogarithmicRigidity
import LogarithmicRigidity.RealLogarithmic
import LogarithmicRigidity.JacobianSyzygies
import LogarithmicRigidity.CaseRNonZero
import LogarithmicRigidity.CounterexampleCert

/-!
# Non-Vacuity and Small-Case Sanity Checks

Concrete small-case evaluations and witness checks ensuring all definitions and
hypotheses are non-vacuous and free of `Nat` subtraction or division junk values.
-/

namespace LogarithmicRigidity

example : Hnodal 1 = 0 := by rfl
example : Hnodal 2 = 1 := by rfl
example : Hnodal 3 = 1 := by rfl
example : Hnodal 4 = 4 := by rfl
example : hBound 0 = 0 := by rfl
example : hBound 1 = 0 := by rfl
example : hBound 2 = 1 := by rfl
example : hBound 3 = 1 := by rfl
example : hBound 4 = 4 := by rfl
example : rNonZeroBound 1 = 0 := by rfl
example : rNonZeroBound 2 = 1 := by rfl
example : rNonZeroBound 3 = 2 := by rfl
example : rNonZeroBound 4 = 5 := by rfl

/-- Non-vacuity witness for `StandardSystemData 1` (`x' = x, y' = -y`, `Hnodal 1 = 0`). -/
example : ∃ sys : StandardSystemData 1, sys.numLimitCycles = Hnodal 1 := by
  refine ⟨{
    hm := le_rfl
    foliationDeg := 1
    foliationDeg_le := le_rfl
    curve := {
      realAffineDegs := [1, 1]
      realAffineDegs_pos := by intro d hd; simp at hd; omega
      hasLineAtInfinity := true
      nonRealPairDegs := []
      nonRealPairDegs_pos := by intro d hd; simp at hd
    }
    numLimitCycles := 0
    zero_if_radial := by intro h; omega
    carnicer_deg := by intro _; simp [RealCurveSplit.totalDeg]
    line_inf_if_full := by intro _; rfl
    harnack_bound := by decide
    log_obstruction := by intro _ _ h; omega
  }, rfl⟩

/-- Non-vacuity witness for `RNonZeroSystemData 3` attaining the sharp bound `2 > Hnodal 3 = 1`. -/
example : ∃ sys : RNonZeroSystemData 3, sys.numLimitCycles = 2 ∧ Hnodal 3 < sys.numLimitCycles := by
  refine ⟨{
    hm := by omega
    curve := {
      realAffineDegs := [4]
      realAffineDegs_pos := by intro d hd; simp at hd; omega
      hasLineAtInfinity := false
      nonRealPairDegs := []
      nonRealPairDegs_pos := by intro d hd; simp at hd
    }
    numLimitCycles := 2
    no_line_inf := rfl
    carnicer_deg := by simp [RealCurveSplit.totalDeg]
    harnack_bound := by decide
    log_obstruction := by intro h _; simp [RealCurveSplit.totalDeg] at h
    irred_m_plus_one_bound := by intro _ _; decide
  }, rfl, by decide⟩

end LogarithmicRigidity
