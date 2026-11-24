/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.Preliminaries

/-!
# Section 4: The Real-Logarithmic Center Obstruction and the Case `r ≡ 0`

Package 3 module covering:
- Proposition 4.1 (real-logarithmic center obstruction and degree reduction)
- Theorem 1.2 (sharp bound `H_nodal(m)` for standard planar systems `r ≡ 0`)
-/

namespace LogarithmicRigidity

private lemma sum_nonRealPairDegs_pos (S : RealCurveSplit) (hne : S.nonRealPairDegs ≠ []) :
    1 ≤ S.nonRealPairDegs.sum := by
  cases h : S.nonRealPairDegs with
  | nil => exact absurd h hne
  | cons d ds =>
    have hd : 0 < d := S.nonRealPairDegs_pos d (by simp [h])
    simp only [List.sum_cons]
    omega

/-- **Proposition 4.1**: Real-logarithmic center obstruction forces a non-real conjugate pair
and reduces the total degree of real affine irreducible components by at least `2` (or `3` if
`L_∞ ⊂ S`). -/
theorem prop_4_1_real_logarithmic_obstruction (S : RealCurveSplit)
    (obs : RealLogCenterObstruction S) (hlc : obs.hasLimitCycle) :
    S.nonRealPairDegs ≠ [] ∧
    (S.hasLineAtInfinity = false → S.realAffineDegs.sum + 2 ≤ S.totalDeg) ∧
    (S.hasLineAtInfinity = true → S.realAffineDegs.sum + 3 ≤ S.totalDeg) := by
  have hne : S.nonRealPairDegs ≠ [] := obs.no_purely_real_limit_cycle hlc
  have hpos : 1 ≤ S.nonRealPairDegs.sum := sum_nonRealPairDegs_pos S hne
  refine ⟨hne, ?_, ?_⟩
  · intro hinf
    have htot : S.totalDeg = S.realAffineDegs.sum + 2 * S.nonRealPairDegs.sum := by
      simp [RealCurveSplit.totalDeg, hinf]
    omega
  · intro hinf
    have htot : S.totalDeg = S.realAffineDegs.sum + 1 + 2 * S.nonRealPairDegs.sum := by
      simp [RealCurveSplit.totalDeg, hinf]
    omega

/-- **Theorem 1.2**: Sharp upper bound `H_nodal(m)` on algebraic limit cycles for standard
planar polynomial systems (`r ≡ 0`) of degree `m ≥ 1` with non-dicritical invariant curves. -/
theorem theorem_1_2_standard_bound_sharp {m : ℕ} (sys : StandardSystemData m) :
    sys.numLimitCycles ≤ Hnodal m := by
  by_cases h0 : sys.foliationDeg = 0
  · rw [sys.zero_if_radial h0]
    exact Nat.zero_le _
  · have hm' : 1 ≤ sys.foliationDeg := Nat.pos_of_ne_zero h0
    by_cases hlc : sys.numLimitCycles = 0
    · rw [hlc]
      exact Nat.zero_le _
    · have hlc_pos : 0 < sys.numLimitCycles := Nat.pos_of_ne_zero hlc
      have hdeg_le : sys.curve.totalDeg ≤ sys.foliationDeg + 2 := sys.carnicer_deg hm'
      have hsum_le : sys.curve.realAffineDegs.sum ≤ m := by
        by_cases hfull : sys.foliationDeg = m
        · have hinf : sys.curve.hasLineAtInfinity = true := sys.line_inf_if_full hfull
          have htot : sys.curve.totalDeg =
              sys.curve.realAffineDegs.sum + 1 + 2 * sys.curve.nonRealPairDegs.sum := by
            simp [RealCurveSplit.totalDeg, hinf]
          by_cases hmax : sys.curve.totalDeg = sys.foliationDeg + 2
          · have hne : sys.curve.nonRealPairDegs ≠ [] :=
              sys.log_obstruction hm' hmax hlc_pos
            have hpos : 1 ≤ sys.curve.nonRealPairDegs.sum :=
              sum_nonRealPairDegs_pos sys.curve hne
            omega
          · omega
        · have hlt : sys.foliationDeg ≤ m - 1 := by
            have := sys.foliationDeg_le
            omega
          by_cases hmax : sys.curve.totalDeg = m + 1
          · have hdeg_eq : sys.curve.totalDeg = sys.foliationDeg + 2 := by
              have := sys.hm
              omega
            have hne : sys.curve.nonRealPairDegs ≠ [] :=
              sys.log_obstruction hm' hdeg_eq hlc_pos
            have hpos : 1 ≤ sys.curve.nonRealPairDegs.sum :=
              sum_nonRealPairDegs_pos sys.curve hne
            have htot : sys.curve.realAffineDegs.sum + 2 * sys.curve.nonRealPairDegs.sum ≤
                sys.curve.totalDeg := by
              unfold RealCurveSplit.totalDeg
              split <;> omega
            omega
          · have htot : sys.curve.realAffineDegs.sum ≤ sys.curve.totalDeg := by
              unfold RealCurveSplit.totalDeg
              split <;> omega
            have := sys.hm
            omega
      calc
        sys.numLimitCycles ≤ (sys.curve.realAffineDegs.map hBound).sum := sys.harnack_bound
        _ ≤ hBound sys.curve.realAffineDegs.sum :=
          lemma_2_4_hBound_mono_superadd.2.2 sys.curve.realAffineDegs
        _ ≤ hBound m := hBound_mono hsum_le
        _ = Hnodal m := hBound_eq_Hnodal sys.hm

end LogarithmicRigidity
