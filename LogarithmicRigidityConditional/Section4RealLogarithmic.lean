/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import LogarithmicRigidity.Preliminaries
import LogarithmicRigidity.RealLogarithmicCalculus
import LogarithmicRigidityConditional.Section3LogarithmicRigidity

/-!
# Section 4 (Full Manuscript Proofs): Real-Logarithmic Obstruction and Standard Case `r ≡ 0`

Formalizes the complete proofs of:
- **Proposition 4.1**: Any real logarithmic foliation possessing a limit cycle must contain a
  complex-conjugate pair `{G, Ḡ}` of non-real irreducible factors, proved by combining
  Giacomini–Llibre–Viano (1996), the unconditional `C¹` local first-integral constancy proof
  `LogarithmicRigidity.prop_4_1_local_first_integral_const`, and the Implicit Function Theorem.
- **Theorem 1.2**: Every standard planar polynomial system (`r ≡ 0`) of affine degree `m ≥ 1`
  with non-dicritical invariant curves has at most `H_nodal(m)` algebraic limit cycles, and
  this bound is sharp for every `m ≥ 1`.
-/

namespace LogarithmicRigidityConditional

open LogarithmicRigidity

/-- **Proposition 4.1**: Real-logarithmic center obstruction and real-affine degree reduction.
Directly invokes `LogarithmicRigidity.prop_4_1_local_first_integral_const` to prove that a
purely real logarithmic foliation forces constancy of `ũ = f₁ ∏ |f_i|^{λ_i/λ₁}` along orbits. -/
theorem prop_4_1_real_logarithmic_obstruction
    (F : ProjectiveFoliation) (S_alg : ReducedCurve) (S : RealCurveDecomposition)
    (numLimitCycles : ℕ)
    (hreal : RealDecompositionOf S_alg S)
    (hlog : ∃ lam, FormEqualsLogarithmicSum F S_alg lam ∧ IsLogarithmicFoliation F S_alg lam)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles)
    (hpos : 0 < numLimitCycles) :
    S.nonRealPairDegs ≠ [] ∧
    (S.hasLineAtInfinity = false → S.realAffineDegs.sum + 2 ≤ S.totalDeg) ∧
    (S.hasLineAtInfinity = true → S.realAffineDegs.sum + 3 ≤ S.totalDeg) := by
  have hne : S.nonRealPairDegs ≠ [] := by
    intro hreal_only
    obtain ⟨n, lam₁, lam, f₁, f₁', f, f', hlam₁, hf₁, hf, hne_f, hlog_ode, hiso⟩ :=
      giacomini_llibre_viano_limit_cycle_orbit F S_alg S numLimitCycles hreal hlog hlc hpos
        hreal_only
    have hconst := prop_4_1_local_first_integral_const (Finset.univ : Finset (Fin n))
      lam₁ hlam₁ lam f₁ f₁' f f' hf₁ (fun i _ t ↦ hf i t) (fun i _ t ↦ hne_f i t) hlog_ode
    exact ift_local_first_integral_contradicts_isolation lam₁ lam f₁ f hiso hconst
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
    (hreal : RealDecompositionOf S_alg S)
    (htot_eq : S_alg.totalDeg = S.totalDeg)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles)
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
      harnack_total_oval_bound S numLimitCycles hlc
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
          have hred := (prop_4_1_real_logarithmic_obstruction F S_alg S numLimitCycles
            hreal hthm11 hlc (by omega)).2.2 hLinf
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
          have hobs := prop_4_1_real_logarithmic_obstruction F S_alg S numLimitCycles
            hreal hthm11 hlc (by omega)
          have hD : S.realAffineDegs.sum ≤ m := by
            cases hL : S.hasLineAtInfinity
            · have := hobs.2.1 hL; omega
            · have := hobs.2.2 hL; omega
          exact hfrom_D hD
      · have hD : S.realAffineDegs.sum ≤ m := by
          unfold RealCurveDecomposition.totalDeg at hdeg_bound hmax
          omega
        exact hfrom_D hD

/-- **Theorem 1.2 (Sharpness)**: For every `m ≥ 1`, there exists a standard degree-`m` planar
polynomial system (`r ≡ 0`, `L_∞` invariant) with non-dicritical invariant curves attaining
exactly `H_nodal(m)` algebraic limit cycles (`ẋ = x, ẏ = -y` for `m = 1`, Christopher [8] for `m ≥ 2`). -/
theorem theorem_1_2_standard_sharpness {m : ℕ} (hm : 1 ≤ m) :
    ∃ (F : ProjectiveFoliation) (S_alg : ReducedCurve) (S : RealCurveDecomposition),
      F.deg = m ∧ F.isSaturated ∧ IsNonDicriticalInvariant F S_alg ∧
      RealDecompositionOf S_alg S ∧ S_alg.totalDeg = S.totalDeg ∧
      S.hasLineAtInfinity = true ∧ HasAlgebraicLimitCycles S (Hnodal m) :=
  christopher_sharpness_construction m hm

end LogarithmicRigidityConditional
