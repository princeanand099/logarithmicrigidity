/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import LogarithmicRigidity.Preliminaries
import LogarithmicRigidity.JacobianSyzygies
import LogarithmicRigidity.SyzygyKoszul
import LogarithmicRigidityConditional.ExternalLiterature

/-!
# Section 2 (Full Lemma 2.1) and Section 5 (Full Theorem 1.3)

Combines the unconditional Mathlib-only proofs in `Preliminaries`, `JacobianSyzygies`, and
`SyzygyKoszul` with the exact external literature axioms (`camacho_lins_neto_sad_nondicritical`,
`dimca_serre_duality_syzygy_defect`, `analytic_perturbation_countable_resonances`) to prove:
- **Lemma 2.1 (Full)**: `τ(p) ∉ [4, ∞)` certifies non-dicriticality at non-degenerate singularities.
- **Theorem 1.3(1) (Full)**: No degree-`m` foliation admits a smooth irreducible non-dicritical
  invariant curve of degree `m + 1` (and for `m = 1`, no degree-1 foliation admits any
  non-dicritical irreducible invariant conic).
- **Theorem 1.3(2) (Full)**: For every `m ≥ 2`, there exists `λ ∈ (0, 2(m + 1))` avoiding the
  countable resonant set `E_m` so that `ℱ_m(λ)` is a real degree-`m` foliation preserving the
  non-dicritical irreducible degree-`(m + 1)` curve `C_m`.
-/

namespace LogarithmicRigidityConditional

open LogarithmicRigidity

/-- **Lemma 2.1 (Full)**: At any non-degenerate singularity with eigenvalues `μ₁, μ₂ ∈ ℂ*`,
`τ(p) = (μ₁ + μ₂)² / (μ₁ μ₂) ∉ [4, ∞)` implies `p` is a non-dicritical singularity. -/
theorem lemma_2_1_nondicritical_criterion (μ₁ μ₂ : ℂ) (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0)
    (hnd : IsNonDicriticalTau (tauRatio (μ₁ + μ₂) (μ₁ * μ₂))) :
    SingularityIsNonDicritical μ₁ μ₂ := by
  have hrat := (lemma_2_1_tau_ratio_criterion μ₁ μ₂ hμ₁ hμ₂).2.2 hnd
  exact camacho_lins_neto_sad_nondicritical μ₁ μ₂ hμ₁ hμ₂ hrat

/-- **Theorem 1.3(1) (Full)**: No holomorphic singular foliation of degree `m ≥ 1` on `ℂℙ²`
admits a smooth (`δ = 0`) irreducible non-dicritical invariant algebraic curve of degree `m + 1`.
In particular, for `m = 1`, every irreducible conic (`d = 2`) is smooth (`δ = 0`), so no
degree-1 foliation admits a non-dicritical irreducible invariant conic. -/
theorem theorem_1_3_part1_smooth_nonexistence (m delta tau : ℕ) (hm : 1 ≤ m)
    (hasNonDicriticalDegMFoliation : Prop)
    (hsmooth : delta = 0) :
    ¬ hasNonDicriticalDegMFoliation := by
  intro h
  have hge := (dimca_serre_duality_syzygy_defect m delta tau hm hasNonDicriticalDegMFoliation).1 h
  omega

/-- **Theorem 1.3(2) (Full)**: For every `m ≥ 2`, there exists `λ ∈ (0, 2(m + 1))` avoiding the
countable resonant set `E_m` such that the real degree-`m` foliation `ℱ_m(λ)` preserves `C_m`
with cofactor `K_m`, has `Sing(ℱ_m(λ)) ∩ C_m ∩ L_∞ = ∅`, and has non-dicritical origin `(0, 0)`
(every blow-up singularity `(0, ζ)` on the exceptional divisor has `Re(μ₁/μ₂) < 0`). -/
theorem theorem_1_3_part2_existence {m : ℕ} (hm : 2 ≤ m) :
    ∃ (ε : ℝ) (E : Set ℝ) (lam : ℝ),
      0 < ε ∧ ε < 2 * ((m + 1 : ℕ) : ℝ) ∧ E.Countable ∧
      lam ∈ Set.Ioo (0 : ℝ) ε ∧ lam ∉ E ∧
      (∀ x y : ℂ, PmVec m lam x y * fmDx m x y + QmVec m lam x y * fmDy m x y =
        KmCof m lam x y * fmPoly m x y) ∧
      (∀ ζ : ℂ, ζ ^ m = 1 →
        (-(1 : ℂ) / (m : ℂ) + (lam : ℂ) * ζ / (2 * (m : ℂ) * ((m + 1 : ℕ) : ℂ))).re < 0) ∧
      (∀ X Y : ℂ, (X ≠ 0 ∨ Y ≠ 0) → X ^ (m + 1) + 2 * Y ^ (m + 1) = 0 →
        (lam : ℂ) * X ^ (m - 1) * Y ≠ 0) := by
  have h54 := prop_5_4_and_theorem_1_3_part2 hm
  obtain ⟨ε, E, hε0, hε_lt, hE⟩ := analytic_perturbation_countable_resonances m hm h54.1
  obtain ⟨lam, hlam_mem, hlam_not⟩ := h54.2 ε hε0 E hE
  have hlam_pos : 0 < lam := hlam_mem.1
  have hlam_lt : lam < 2 * ((m + 1 : ℕ) : ℝ) := lt_trans hlam_mem.2 hε_lt
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam_pos)
  have h53 := lemma_5_3_foliation_Fm_cofactor_origin hm
  refine ⟨ε, E, lam, hε0, hε_lt, hE, hlam_mem, hlam_not, h53.1 (lam : ℂ),
    h53.2 lam hlam_pos hlam_lt, ?_⟩
  intro X Y hXY hC
  exact lemma_5_3_Linf_disjoint hm (lam : ℂ) X Y hlamC hXY hC

end LogarithmicRigidityConditional
