/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import LogarithmicRigidityConditional.ExternalLiterature

/-!
# Section 3 (Full Manuscript Proofs): Logarithmic Rigidity at Degree `m + 2`

Formalizes the complete proofs of:
- **Lemma 3.1**: Inductive blow-up propagation of `η_j = h_j ω_j / f_j` along an embedded
  log-resolution `π : X̃ → ℂℙ²`, proving `ord(h_j) : ℤ` is non-decreasing and `≥ 0` at every stage.
- **Proposition 3.2**: Global logarithmic pullback `α = π*η ∈ H⁰(X̃, Ω¹_{X̃}(log D))` is closed,
  with nonzero constant Poincaré residues satisfying `∑ λ_i deg F_i = 0`.
- **Theorem 1.1**: Every reduced non-dicritical invariant curve `S` of degree `m + 2` of a
  degree-`m` foliation (`m ≥ 1`) forces `ℱ` to be logarithmic and `k ≥ 3` irreducible components.
-/

namespace LogarithmicRigidityConditional

/-- Auxiliary structural-recursion definition of the cumulative signed holomorphic factor order
`ord(h_j) ∈ ℤ` along an embedded log-resolution `res` (Lemma 3.1). -/
def cumulativeOrderAux {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) : ℕ → ℤ
  | 0 => 0
  | j + 1 =>
      if hj : j < res.N then
        cumulativeOrderAux res j +
          (((res.steps ⟨j, hj⟩).nuF : ℤ) + 1 - ((res.steps ⟨j, hj⟩).nuC : ℤ))
      else cumulativeOrderAux res j

/-- Cumulative signed holomorphic factor order `ord(h_j) ∈ ℤ` along an embedded
log-resolution `res` (Lemma 3.1). Using `ℤ` avoids saturating `ℕ` subtraction. -/
def cumulativeOrder {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) (j : Fin (res.N + 1)) : ℤ :=
  cumulativeOrderAux res j.val

/-- **Lemma 3.1**: Along every stage `j` of an embedded log-resolution `res` of a reduced
non-dicritical invariant curve `S`, the blow-up multiplicity inequality
`ν_p(C_{j-1}) ≤ ν_p(ℱ_{j-1}) + 1` holds and the signed cumulative order
`ord(h_j) ∈ ℤ` is non-decreasing and non-negative (`0 ≤ ord(h_j)`). -/
theorem lemma_3_1_blowup_propagation {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) :
    (∀ j : Fin res.N, (res.steps j).nuC ≤ (res.steps j).nuF + 1) ∧
    (∀ j : Fin res.N,
      cumulativeOrder res ⟨j.val, by omega⟩ ≤ cumulativeOrder res ⟨j.val + 1, by omega⟩) ∧
    (∀ j : Fin (res.N + 1), 0 ≤ cumulativeOrder res j) := by
  have hstep : ∀ j : Fin res.N, (res.steps j).nuC ≤ (res.steps j).nuF + 1 := by
    intro j
    rcases (res.steps j).isRegularOrNonDicritical with ⟨hF0, hC1⟩ | hnd
    · omega
    · exact carnicer_local_inequality _ _ hnd
  have hmono : ∀ j : Fin res.N,
      cumulativeOrder res ⟨j.val, by omega⟩ ≤ cumulativeOrder res ⟨j.val + 1, by omega⟩ := by
    intro ⟨k, hk⟩
    have hj : (res.steps ⟨k, hk⟩).nuC ≤ (res.steps ⟨k, hk⟩).nuF + 1 := hstep ⟨k, hk⟩
    simp only [cumulativeOrder, cumulativeOrderAux, hk, ↓reduceDIte]
    omega
  have hnonneg : ∀ j : Fin (res.N + 1), 0 ≤ cumulativeOrder res j := by
    intro ⟨k, hk⟩
    induction k with
    | zero =>
      simp only [cumulativeOrder, cumulativeOrderAux]
      exact le_rfl
    | succ k ih =>
      have hk_prev : k < res.N + 1 := by omega
      have h0 := ih hk_prev
      have h1 := hmono ⟨k, by omega⟩
      exact le_trans h0 h1
  exact ⟨hstep, hmono, hnonneg⟩

/-- **Proposition 3.2**: For a saturated degree-`m` foliation `ℱ` and a reduced non-dicritical
invariant curve `S` of degree `m + 2`, the pullback `α = π*η` is logarithmic and closed, and
its Poincaré residues `λ_i` along `S̃_i` are nonzero constants summing with degree weights to `0`. -/
theorem prop_3_2_logarithmic_residues {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) (hsat : F.isSaturated)
    (hdeg : S.totalDeg = F.deg + 2) :
    PullbackIsLogarithmic res ∧
    PullbackIsClosed res ∧
    (∀ i : Fin S.k, poincareResidue res i ≠ 0) ∧
    (∑ i : Fin S.k, poincareResidue res i * (S.degF i : ℂ)) = 0 := by
  have hlog : PullbackIsLogarithmic res :=
    log_order_nonneg_implies_logarithmic res (lemma_3_1_blowup_propagation res).1
  have hclosed : PullbackIsClosed res := deligne_logarithmic_closed res hlog
  have hres := residue_theorem_CP1 res hsat hdeg hclosed
  exact ⟨hlog, hclosed, hres.1, hres.2⟩

/-- **Theorem 1.1**: Let `ℱ` be a saturated holomorphic singular foliation of degree `m ≥ 1`
on `ℂℙ²` and `S = {F₁ ··· F_k = 0}` a reduced non-dicritical `ℱ`-invariant curve of degree
`m + 2`. Then:
1. `ℱ` is a logarithmic foliation: `ω/F = ∑ λ_i dF_i/F_i` with `λ_i ∈ ℂ*` and `∑ λ_i deg F_i = 0`.
2. Necessarily `k ≥ 3` (in particular, no non-dicritical irreducible invariant curve of degree
   `m + 2` exists). -/
theorem theorem_1_1_logarithmic_rigidity (F : ProjectiveFoliation) (S : ReducedCurve)
    (hm : 1 ≤ F.deg) (hsat : F.isSaturated) (hnd : IsNonDicriticalInvariant F S)
    (hdeg : S.totalDeg = F.deg + 2) :
    (∃ lam : Fin S.k → ℂ,
      FormEqualsLogarithmicSum F S lam ∧ IsLogarithmicFoliation F S lam) ∧
    3 ≤ S.k := by
  obtain ⟨res⟩ := embedded_log_resolution_exists F S hnd
  obtain ⟨_, _, hlam_ne, hsum⟩ := prop_3_2_logarithmic_residues res hsat hdeg
  have hform : FormEqualsLogarithmicSum F S (poincareResidue res) :=
    hartogs_and_no_holomorphic_1forms_CP2 res hsum
  refine ⟨⟨poincareResidue res, hform, hlam_ne, hsum⟩, ?_⟩
  by_contra hlt
  push Not at hlt
  have hk_cases : S.k = 0 ∨ S.k = 1 ∨ S.k = 2 := by omega
  rcases hk_cases with hk0 | hk1 | hk2
  · have htot0 : S.totalDeg = 0 := by
      unfold ReducedCurve.totalDeg
      exact Finset.sum_eq_zero fun i _ ↦ (Nat.not_lt_zero i.val (hk0 ▸ i.isLt)).elim
    omega
  · let i0 : Fin S.k := ⟨0, by omega⟩
    have hsum1 : poincareResidue res i0 * (S.degF i0 : ℂ) = 0 := by
      have huniv : (Finset.univ : Finset (Fin S.k)) = {i0} := by
        ext x; simp [i0, Fin.ext_iff]; omega
      rw [huniv, Finset.sum_singleton] at hsum
      exact hsum
    have hd0 : (S.degF i0 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (S.degF_pos i0))
    exact hlam_ne i0 ((mul_eq_zero.mp hsum1).resolve_right hd0)
  · let i0 : Fin S.k := ⟨0, by omega⟩
    let i1 : Fin S.k := ⟨1, by omega⟩
    have hsum2 : poincareResidue res i0 * (S.degF i0 : ℂ) +
        poincareResidue res i1 * (S.degF i1 : ℂ) = 0 := by
      have huniv : (Finset.univ : Finset (Fin S.k)) = {i0, i1} := by
        ext x; simp [i0, i1, Fin.ext_iff]; omega
      have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
      rw [huniv, Finset.sum_pair hne] at hsum
      exact hsum
    let d0 := S.degF i0
    let d1 := S.degF i1
    let g := Nat.gcd d0 d1
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d1 (S.degF_pos i0)
    have hd0_dvd : g ∣ d0 := Nat.gcd_dvd_left d0 d1
    have hd1_dvd : g ∣ d1 := Nat.gcd_dvd_right d0 d1
    let a := d1 / g
    let b := d0 / g
    have ha_pos : 0 < a := Nat.div_pos (Nat.le_of_dvd (S.degF_pos i1) hd1_dvd) hg_pos
    have hb_pos : 0 < b := Nat.div_pos (Nat.le_of_dvd (S.degF_pos i0) hd0_dvd) hg_pos
    have hbg : b * g = d0 := Nat.div_mul_cancel hd0_dvd
    have hag : a * g = d1 := Nat.div_mul_cancel hd1_dvd
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg_pos)
    have hrel : poincareResidue res i0 * (b : ℂ) + poincareResidue res i1 * (a : ℂ) = 0 := by
      have hmul : (poincareResidue res i0 * (b : ℂ) + poincareResidue res i1 * (a : ℂ)) *
          (g : ℂ) = 0 := by
        have hbC : (b : ℂ) * (g : ℂ) = (d0 : ℂ) := by exact_mod_cast hbg
        have haC : (a : ℂ) * (g : ℂ) = (d1 : ℂ) := by exact_mod_cast hag
        calc
          (poincareResidue res i0 * (b : ℂ) + poincareResidue res i1 * (a : ℂ)) * (g : ℂ)
              = poincareResidue res i0 * ((b : ℂ) * (g : ℂ)) +
                poincareResidue res i1 * ((a : ℂ) * (g : ℂ)) := by ring
          _ = poincareResidue res i0 * (d0 : ℂ) + poincareResidue res i1 * (d1 : ℂ) := by
                rw [hbC, haC]
          _ = 0 := hsum2
      exact (mul_eq_zero.mp hmul).resolve_right hgC
    have hH : HasTwoComponentRationalFirstIntegral F S hk2 a b :=
      logarithmic_two_component_gives_first_integral F S hk2 (poincareResidue res) a b
        ha_pos hb_pos hform (hlam_ne i0) hrel
    exact bezout_rational_first_integral_dicritical F S hk2 a b ha_pos hb_pos hH hnd

end LogarithmicRigidityConditional
