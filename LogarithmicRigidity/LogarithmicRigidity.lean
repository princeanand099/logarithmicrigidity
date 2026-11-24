/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs

/-!
# Section 3: Logarithmic Rigidity at Degree `m + 2`

Package 2 module covering:
- Lemma 3.1 (inductive blow-up propagation of `η_j = h_j ω_j / f_j`)
- Proposition 3.2 (global logarithmic pullback and residue sum `∑ λ_i deg F_i = 0`)
- Theorem 1.1 (logarithmic rigidity and `k ≥ 3` components)
-/

namespace LogarithmicRigidity

/-- Local blow-up chart algebra (`x = u`, `y = u * v`, `dy = v du + u dv`):
pulling back `A dx + B dy` yields `(A + v * B) du + (u * B) dv`. -/
lemma blowup_chart_pullback_algebra {R : Type*} [CommRing R] (A B u v du dv : R) :
    A * du + B * (v * du + u * dv) = (A + v * B) * du + (u * B) * dv := by
  ring

/-- Weight-0 homogeneity of a logarithmic quotient `ω / F` when `ω` and `F` have matching
homogeneity degree `d`. -/
lemma euler_weight_zero_scaling {F : Type*} [Field F] (d : ℕ) {t ω f : F}
    (ht : t ≠ 0) :
    (t ^ d * ω) / (t ^ d * f) = ω / f :=
  mul_div_mul_left ω f (pow_ne_zero d ht)

/-- At each blow-up step, Carnicer's non-dicriticality bound `ν_p(C) ≤ ν_p(ℱ) + 1` ensures
that the signed exponent increment `(ν_p(ℱ) + 1) - ν_p(C)` is non-negative. -/
lemma blowup_step_increment_nonneg (step : BlowUpStepData) :
    (0 : ℤ) ≤ (step.nuF : ℤ) + 1 - (step.nuC : ℤ) := by
  have h := step.nonDicritical
  omega

/-- Single-step monotonicity of `cumulativeOrder` along the blow-up sequence. -/
lemma cumulativeOrder_succ_ge {N : ℕ} (res : LogResolutionData N)
    (k : ℕ) (hk : k + 1 < N + 1) :
    cumulativeOrder res ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ cumulativeOrder res ⟨k + 1, hk⟩ := by
  dsimp [cumulativeOrder]
  omega

/-- **Lemma 3.1**: Inductive blow-up propagation preserves non-negativity of the holomorphic
factor exponent along every stage of an embedded log-resolution. -/
theorem lemma_3_1_blowup_propagation {N : ℕ} (res : LogResolutionData N)
    (j : Fin (N + 1)) :
    res.initialOrder ≤ cumulativeOrder res j := by
  rcases j with ⟨n, hn⟩
  induction n with
  | zero =>
    simp [cumulativeOrder]
  | succ k ih =>
    exact le_trans (ih (Nat.lt_of_succ_lt hn)) (cumulativeOrder_succ_ge res k hn)

/-- **Proposition 3.2**: Global logarithmic pullback has nonzero constant residues summing
with degree weights to zero. -/
theorem prop_3_2_logarithmic_residues {m : ℕ} {S : InvariantCurveDecomposition}
    (data : Section3ClassicalData m S) :
    (∀ i : Fin S.k, data.residues.lam i ≠ 0) ∧
    (∑ i : Fin S.k, data.residues.lam i * (S.degF i : ℂ)) = 0 :=
  ⟨data.residues.lam_ne_zero, data.residues.residue_sum_zero⟩

/-- **Theorem 1.1**: Logarithmic rigidity at degree `m + 2` and `k ≥ 3` irreducible components
(no non-dicritical irreducible invariant curve of degree `m + 2`). -/
theorem theorem_1_1_logarithmic_rigidity {m : ℕ} (hm : 1 ≤ m)
    {S : InvariantCurveDecomposition} (data : Section3ClassicalData m S) :
    (∀ i : Fin S.k, data.residues.lam i ≠ 0) ∧
    (∑ i : Fin S.k, data.residues.lam i * (S.degF i : ℂ)) = 0 ∧
    3 ≤ S.k := by
  refine ⟨data.residues.lam_ne_zero, data.residues.residue_sum_zero, ?_⟩
  by_contra hk_lt
  have hcases : S.k = 0 ∨ S.k = 1 ∨ S.k = 2 := by omega
  rcases hcases with hk | hk | hk
  · have htot : S.totalDeg = 0 := by
      unfold InvariantCurveDecomposition.totalDeg
      apply Finset.sum_eq_zero
      intro i _
      have := i.isLt
      omega
    have hdeg := data.deg_eq
    omega
  · let i0 : Fin S.k := ⟨0, by omega⟩
    have huniv : (Finset.univ : Finset (Fin S.k)) = {i0} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      ext
      have := i.isLt
      omega
    have hsum := data.residues.residue_sum_zero
    rw [huniv, Finset.sum_singleton] at hsum
    have hlam : data.residues.lam i0 ≠ 0 := data.residues.lam_ne_zero i0
    have hdeg_pos : 0 < S.degF i0 := S.degF_pos i0
    have hdeg_ne : (S.degF i0 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero hlam hdeg_ne hsum
  · let i0 : Fin S.k := ⟨0, by omega⟩
    let i1 : Fin S.k := ⟨1, by omega⟩
    have hi_ne : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    have huniv : (Finset.univ : Finset (Fin S.k)) = {i0, i1} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hi := i.isLt
      by_cases h0 : i.val = 0
      · left; exact Fin.ext h0
      · right; exact Fin.ext (by omega)
    have hsum := data.residues.residue_sum_zero
    rw [huniv, Finset.sum_pair hi_ne] at hsum
    exact data.no_two_component_first_integral hk (S.degF i1) (S.degF i0)
      (S.degF_pos i1) (S.degF_pos i0) (by dsimp [i0, i1]; ring) hsum

end LogarithmicRigidity
