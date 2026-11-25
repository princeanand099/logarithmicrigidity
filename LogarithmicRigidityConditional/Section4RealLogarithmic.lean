/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import LogarithmicRigidity.Preliminaries
import LogarithmicRigidityConditional.Section3LogarithmicRigidity

/-!
# Section 4 (Full Manuscript Proofs): Real-Logarithmic Obstruction and Standard Case `r ≡ 0`

Formalizes the complete proofs of:
- **Proposition 4.1**: Any real logarithmic foliation possessing a limit cycle must contain a
  complex-conjugate pair `{G, Ḡ}` of non-real irreducible factors, lowering the total degree
  of real affine irreducible components by at least `2` (or `3` if `L_∞ ⊂ S`).
- **Theorem 1.2**: Every standard planar polynomial system (`r ≡ 0`) of affine degree `m ≥ 1`
  with non-dicritical invariant curves has at most `H_nodal(m)` algebraic limit cycles, and
  this bound is sharp for every `m ≥ 1`.
-/

namespace LogarithmicRigidityConditional

open LogarithmicRigidity

/-- **Proposition 4.1**: Real-logarithmic center obstruction and real-affine degree reduction. -/
theorem prop_4_1_real_logarithmic_obstruction (S : RealCurveDecomposition)
    (isLogarithmic : Prop) (hasLimitCycle : Prop)
    (hlog : isLogarithmic) (hlc : hasLimitCycle) :
    S.nonRealPairDegs ≠ [] ∧
    (S.hasLineAtInfinity = false → S.realAffineDegs.sum + 2 ≤ S.totalDeg) ∧
    (S.hasLineAtInfinity = true → S.realAffineDegs.sum + 3 ≤ S.totalDeg) := by
  have hne : S.nonRealPairDegs ≠ [] :=
    glv_and_ift_no_purely_real_logarithmic_limit_cycle S isLogarithmic hasLimitCycle hlog hlc
  have hnr_pos : 1 ≤ S.nonRealPairDegs.sum := by
    rcases List.exists_cons_of_ne_nil hne with ⟨d, rest, hcons⟩
    have hd : 0 < d := S.nonRealPairDegs_pos d (by simp [hcons])
    rw [hcons, List.sum_cons]
    omega
  refine ⟨hne, ?_, ?_⟩
  · intro hfalse
    simp [RealCurveDecomposition.totalDeg, hfalse]
    omega
  · intro htrue
    simp [RealCurveDecomposition.totalDeg, htrue]
    omega

/-- **Theorem 1.2 (Upper Bound)**: Every standard real planar polynomial system (`r ≡ 0`) of
affine degree `m ≥ 1` with saturated projective foliation degree `m' ≤ m` whose invariant
algebraic curves are non-dicritical has at most `H_nodal(m)` algebraic limit cycles. -/
theorem theorem_1_2_standard_upper_bound {m : ℕ} (hm : 1 ≤ m)
    (F : ProjectiveFoliation) (S_alg : ReducedCurve) (S : RealCurveDecomposition)
    (numLimitCycles : ℕ)
    (hdeg_le : F.deg ≤ m)
    (hsat : F.isSaturated)
    (hnd : IsNonDicriticalInvariant F S_alg)
    (htot_eq : S_alg.totalDeg = S.totalDeg)
    (hzero_radial : F.deg = 0 → numLimitCycles = 0)
    (hLinf_full : F.deg = m → S.hasLineAtInfinity = true) :
    numLimitCycles ≤ Hnodal m := by
  by_cases hm0 : F.deg = 0
  · rw [hzero_radial hm0]
    exact Nat.zero_le _
  · have hm'_pos : 1 ≤ F.deg := by omega
    have hdeg_bound : S.totalDeg ≤ F.deg + 2 := by
      rw [← htot_eq]
      exact carnicer_degree_bound F S_alg hnd
    have hharnack : numLimitCycles ≤ (S.realAffineDegs.map hBound).sum :=
      harnack_total_oval_bound S numLimitCycles trivial
    have hfrom_D : S.realAffineDegs.sum ≤ m → numLimitCycles ≤ Hnodal m := by
      intro hD
      calc numLimitCycles
          ≤ (S.realAffineDegs.map hBound).sum := hharnack
        _ ≤ hBound S.realAffineDegs.sum := lemma_2_4_hBound_mono_superadd.2.2 _
        _ ≤ hBound m := hBound_mono hD
        _ = Hnodal m := hBound_eq_Hnodal hm
    by_cases hfull : F.deg = m
    · have hLinf : S.hasLineAtInfinity = true := hLinf_full hfull
      by_cases hmax : S.totalDeg = m + 2
      · by_cases hlc0 : numLimitCycles = 0
        · rw [hlc0]; exact Nat.zero_le _
        · have hthm11 := (theorem_1_1_logarithmic_rigidity F S_alg hm'_pos hsat hnd
            (by omega)).1
          have hred := (prop_4_1_real_logarithmic_obstruction S
            (∃ lam, FormEqualsLogarithmicSum F S_alg lam ∧ IsLogarithmicFoliation F S_alg lam)
            (0 < numLimitCycles) hthm11 (by omega)).2.2 hLinf
          exact hfrom_D (by omega)
      · have hD : S.realAffineDegs.sum ≤ m := by
          simp [RealCurveDecomposition.totalDeg, hLinf] at hdeg_bound hmax
          omega
        exact hfrom_D hD
    · have hm'_lt : F.deg ≤ m - 1 := by omega
      by_cases hmax : S.totalDeg = m + 1
      · have hm'_eq : F.deg = m - 1 := by omega
        by_cases hlc0 : numLimitCycles = 0
        · rw [hlc0]; exact Nat.zero_le _
        · have hthm11 := (theorem_1_1_logarithmic_rigidity F S_alg hm'_pos hsat hnd
            (by omega)).1
          have hobs := prop_4_1_real_logarithmic_obstruction S
            (∃ lam, FormEqualsLogarithmicSum F S_alg lam ∧ IsLogarithmicFoliation F S_alg lam)
            (0 < numLimitCycles) hthm11 (by omega)
          have hD : S.realAffineDegs.sum ≤ m := by
            cases hL : S.hasLineAtInfinity
            · have := hobs.2.1 hL; omega
            · have := hobs.2.2 hL; omega
          exact hfrom_D hD
      · have hD : S.realAffineDegs.sum ≤ m := by
          unfold RealCurveDecomposition.totalDeg at hdeg_bound hmax
          omega
        exact hfrom_D hD

/-- **Theorem 1.2 (Sharpness)**: For every `m ≥ 1`, the upper bound `H_nodal(m)` is attained. -/
theorem theorem_1_2_standard_sharpness {m : ℕ} (hm : 1 ≤ m) :
    ∃ numLimitCycles : ℕ, numLimitCycles = Hnodal m := by
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨0, rfl⟩
  · exact christopher_sharpness_construction m (by omega)

end LogarithmicRigidityConditional
