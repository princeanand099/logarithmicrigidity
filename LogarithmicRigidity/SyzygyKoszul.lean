/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.JacobianSyzygies

/-!
# Section 5 (Algebraic Core): Jacobian Syzygy Correspondence, Koszul Rigidity, and Parametrization

Proves directly on top of Mathlib `v4.35.0` (`MvPolynomial (Fin 3) ℂ`):
- `prop_5_1_syzygy_correspondence`: Proposition 5.1(1) bijection between invariant 1-forms
  `ω = i_V i_E Ω` (`i_E ω = 0`, `ω ∧ dF ≡ 0 (mod F)`) and Jacobian syzygies `Syz(J_F)`.
- `prop_5_1_koszul_pencil_forms`: Proposition 5.1(3) correspondence between the 3-dimensional
  Koszul subspace and the logarithmic pencil forms `ω_L = L dF - d F dL`.
- `theorem_1_3_part1_koszul_rigidity`: Algebraic core of Theorem 1.3(1): whenever the Jacobian
  partial derivatives `(F_X, F_Y, F_Z)` form a regular sequence in `ℂ[X, Y, Z]`, every
  homogeneous degree-`(d - 1)` Jacobian syzygy is a `ℂ`-linear combination of the three Koszul
  syzygies, and its induced 1-form is `ω_L = L dF - d F dL`.
- `lemma_5_2_Linf_smooth`, `lemma_5_3_Linf_disjoint`, `prop_5_4_param_factorization`:
  Smoothness of `C_m` along `L_∞`, disjointness `Sing(ℱ_m(λ)) ∩ C_m ∩ L_∞ = ∅`, and the exact
  rational parametrization factorization of `(P_m, Q_m)` in terms of `g_m(t; λ)`.
-/

namespace LogarithmicRigidity

private lemma euler_expanded (F : MvPolynomial (Fin 3) ℂ) (d : ℕ) (hF : F.IsHomogeneous d) :
    MvPolynomial.X 0 * MvPolynomial.pderiv 0 F +
    MvPolynomial.X 1 * MvPolynomial.pderiv 1 F +
    MvPolynomial.X 2 * MvPolynomial.pderiv 2 F = (d : MvPolynomial (Fin 3) ℂ) * F := by
  have h := prop_5_1_euler_homogeneous F d hF
  simpa [Fin.sum_univ_three] using h

private lemma isHomogeneous_pderiv (F : MvPolynomial (Fin 3) ℂ) (d : ℕ) (hd : 1 ≤ d)
    (hF : F.IsHomogeneous d) (i : Fin 3) :
    (MvPolynomial.pderiv i F).IsHomogeneous (d - 1) := by
  intro m hm
  rw [MvPolynomial.coeff_pderiv] at hm
  set m' : Fin 3 →₀ ℕ := m + Finsupp.single i 1
  have hne : F.coeff m' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hm
    exact hm rfl
  have hdeg : ∑ j : Fin 3, m' j = d := by
    have hw := hF hne
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hw
  have hsum : ∑ j : Fin 3, m' j = (∑ j : Fin 3, m j) + 1 := by
    simp [m', Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]
  have hmdeg : ∑ j : Fin 3, m j = d - 1 := by omega
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hmdeg

private lemma coeff_mul_of_isHomogeneous (u A : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hA : A.IsHomogeneous k) (m : Fin 3 →₀ ℕ) (hm : ∑ j : Fin 3, m j = k) :
    (u * A).coeff m = u.coeff 0 * A.coeff m := by
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_single (0, m) ?_ ?_
  · rintro ⟨p, q⟩ hpq hne
    have hpq' : p + q = m := by simpa using hpq
    by_cases hq : A.coeff q = 0
    · simp [hq]
    · exfalso
      have hqdeg : ∑ j : Fin 3, q j = k := by
        have hw := hA hq
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hw
      have hsum : ∑ j : Fin 3, p j + ∑ j : Fin 3, q j = k := by
        rw [← Finset.sum_add_distrib]
        have hadd : ∀ j : Fin 3, p j + q j = m j := fun j ↦ by
          rw [← Finsupp.add_apply, hpq']
        simpa [hadd] using hm
      have hp0 : p = 0 := by
        ext j
        have hj : p j ≤ ∑ i : Fin 3, p i :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
      subst hp0
      rw [zero_add] at hpq'
      exact hne (Prod.ext rfl hpq')
  · intro hnot
    exfalso
    exact hnot (by simp)

private lemma eq_const_mul_add_const_mul_of_isHomogeneous
    (P A B u v : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hP : P.IsHomogeneous k) (hA : A.IsHomogeneous k) (hB : B.IsHomogeneous k)
    (heq : P = u * A + v * B) :
    P = MvPolynomial.C (u.coeff 0) * A + MvPolynomial.C (v.coeff 0) * B := by
  ext m
  by_cases hm : ∑ j : Fin 3, m j = k
  · rw [heq]
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]
    rw [coeff_mul_of_isHomogeneous u A k hA m hm,
        coeff_mul_of_isHomogeneous v B k hB m hm]
  · have hP0 : P.coeff m = 0 := by
      by_contra hne
      have hw := hP hne
      exact hm (by simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hw)
    have hA0 : A.coeff m = 0 := by
      by_contra hne
      have hw := hA hne
      exact hm (by simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hw)
    have hB0 : B.coeff m = 0 := by
      by_contra hne
      have hw := hB hne
      exact hm (by simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hw)
    simp [hP0, hA0, hB0]

/-- **Proposition 5.1(1)**: Exact algebraic correspondence between invariant 1-forms
`ω = i_V i_E Ω` (`i_E ω = 0`, `ω ∧ dF ≡ 0 (mod F)`) and Jacobian syzygies `Syz(J_F)`. -/
theorem prop_5_1_syzygy_correspondence (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hd : 1 ≤ d) (hF : F.IsHomogeneous d) (hF_ne : F ≠ 0) :
    (∀ P₁ P₂ P₃ : MvPolynomial (Fin 3) ℂ,
      let ω := formOfSyzygy P₁ P₂ P₃
      MvPolynomial.X 0 * ω.1 + MvPolynomial.X 1 * ω.2.1 + MvPolynomial.X 2 * ω.2.2 = 0 ∧
      ω.1 * MvPolynomial.pderiv 1 F - ω.2.1 * MvPolynomial.pderiv 0 F =
        MvPolynomial.X 2 * (P₁ * MvPolynomial.pderiv 0 F + P₂ * MvPolynomial.pderiv 1 F +
          P₃ * MvPolynomial.pderiv 2 F) - (d : MvPolynomial (Fin 3) ℂ) * P₃ * F ∧
      ω.2.1 * MvPolynomial.pderiv 2 F - ω.2.2 * MvPolynomial.pderiv 1 F =
        MvPolynomial.X 0 * (P₁ * MvPolynomial.pderiv 0 F + P₂ * MvPolynomial.pderiv 1 F +
          P₃ * MvPolynomial.pderiv 2 F) - (d : MvPolynomial (Fin 3) ℂ) * P₁ * F ∧
      ω.2.2 * MvPolynomial.pderiv 0 F - ω.1 * MvPolynomial.pderiv 2 F =
        MvPolynomial.X 1 * (P₁ * MvPolynomial.pderiv 0 F + P₂ * MvPolynomial.pderiv 1 F +
          P₃ * MvPolynomial.pderiv 2 F) - (d : MvPolynomial (Fin 3) ℂ) * P₂ * F) ∧
    (∀ P₁ P₂ P₃ Q₁ Q₂ Q₃ : MvPolynomial (Fin 3) ℂ,
      IsJacobianSyzygy F P₁ P₂ P₃ → IsJacobianSyzygy F Q₁ Q₂ Q₃ →
      formOfSyzygy P₁ P₂ P₃ = formOfSyzygy Q₁ Q₂ Q₃ →
      P₁ = Q₁ ∧ P₂ = Q₂ ∧ P₃ = Q₃) ∧
    (∀ V₁ V₂ V₃ K : MvPolynomial (Fin 3) ℂ,
      V₁ * MvPolynomial.pderiv 0 F + V₂ * MvPolynomial.pderiv 1 F +
        V₃ * MvPolynomial.pderiv 2 F = K * F →
      ∃ P₁ P₂ P₃ : MvPolynomial (Fin 3) ℂ,
        IsJacobianSyzygy F P₁ P₂ P₃ ∧
        formOfSyzygy P₁ P₂ P₃ = formOfSyzygy V₁ V₂ V₃) := by
  have heul := euler_expanded F d hF
  have hd_ne : (d : MvPolynomial (Fin 3) ℂ) ≠ 0 := by
    have hnat : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    intro h0
    have hc : MvPolynomial.C (d : ℂ) = (0 : MvPolynomial (Fin 3) ℂ) := by simpa using h0
    exact hnat (MvPolynomial.C_eq_zero.mp hc)
  have hdF_ne : (d : MvPolynomial (Fin 3) ℂ) * F ≠ 0 := mul_ne_zero hd_ne hF_ne
  refine ⟨?_, ?_, ?_⟩
  · intro P₁ P₂ P₃
    dsimp only [formOfSyzygy]
    refine ⟨by ring, ?_, ?_, ?_⟩
    · linear_combination -P₃ * heul
    · linear_combination -P₁ * heul
    · linear_combination -P₂ * heul
  · intro P₁ P₂ P₃ Q₁ Q₂ Q₃ hP hQ hform
    unfold formOfSyzygy at hform
    have h1 : P₂ * MvPolynomial.X 2 - P₃ * MvPolynomial.X 1 =
        Q₂ * MvPolynomial.X 2 - Q₃ * MvPolynomial.X 1 := congr_arg Prod.fst hform
    have h2 : P₃ * MvPolynomial.X 0 - P₁ * MvPolynomial.X 2 =
        Q₃ * MvPolynomial.X 0 - Q₁ * MvPolynomial.X 2 :=
      congr_arg (fun t ↦ t.2.1) hform
    have h3 : P₁ * MvPolynomial.X 1 - P₂ * MvPolynomial.X 0 =
        Q₁ * MvPolynomial.X 1 - Q₂ * MvPolynomial.X 0 :=
      congr_arg (fun t ↦ t.2.2) hform
    unfold IsJacobianSyzygy at hP hQ
    have hD1 : (P₁ - Q₁) * ((d : MvPolynomial (Fin 3) ℂ) * F) = 0 := by
      linear_combination (P₁ - Q₁) * (-heul) + MvPolynomial.X 0 * (hP - hQ) +
        MvPolynomial.pderiv 1 F * h3 - MvPolynomial.pderiv 2 F * h2
    have hD2 : (P₂ - Q₂) * ((d : MvPolynomial (Fin 3) ℂ) * F) = 0 := by
      linear_combination (P₂ - Q₂) * (-heul) + MvPolynomial.X 1 * (hP - hQ) +
        MvPolynomial.pderiv 2 F * h1 - MvPolynomial.pderiv 0 F * h3
    have hD3 : (P₃ - Q₃) * ((d : MvPolynomial (Fin 3) ℂ) * F) = 0 := by
      linear_combination (P₃ - Q₃) * (-heul) + MvPolynomial.X 2 * (hP - hQ) +
        MvPolynomial.pderiv 0 F * h2 - MvPolynomial.pderiv 1 F * h1
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hD1).resolve_right hdF_ne),
           sub_eq_zero.mp ((mul_eq_zero.mp hD2).resolve_right hdF_ne),
           sub_eq_zero.mp ((mul_eq_zero.mp hD3).resolve_right hdF_ne)⟩
  · intro V₁ V₂ V₃ K hV
    let invd : MvPolynomial (Fin 3) ℂ := MvPolynomial.C ((d : ℂ)⁻¹)
    have hinv : invd * (d : MvPolynomial (Fin 3) ℂ) = 1 := by
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hcast : (d : MvPolynomial (Fin 3) ℂ) = MvPolynomial.C (d : ℂ) := by simp
      rw [hcast, ← map_mul, inv_mul_cancel₀ hdC, map_one]
    refine ⟨V₁ - invd * K * MvPolynomial.X 0,
            V₂ - invd * K * MvPolynomial.X 1,
            V₃ - invd * K * MvPolynomial.X 2, ?_, ?_⟩
    · unfold IsJacobianSyzygy
      linear_combination hV - invd * K * heul - K * F * hinv
    · unfold formOfSyzygy
      refine Prod.ext (by ring) (Prod.ext (by ring) (by ring))

/-- **Proposition 5.1(3)**: The 3-dimensional Koszul subspace corresponds precisely to the
logarithmic pencil forms `ω_L = L dF - (deg F) F dL` for linear forms `L = c₀ X + c₁ Y + c₂ Z`. -/
theorem prop_5_1_koszul_pencil_forms (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hF : F.IsHomogeneous d) (c₀ c₁ c₂ : ℂ) :
    let Fx := MvPolynomial.pderiv 0 F
    let Fy := MvPolynomial.pderiv 1 F
    let Fz := MvPolynomial.pderiv 2 F
    let L := MvPolynomial.C c₀ * MvPolynomial.X 0 +
             MvPolynomial.C c₁ * MvPolynomial.X 1 +
             MvPolynomial.C c₂ * MvPolynomial.X 2
    let P₁ := MvPolynomial.C c₁ * Fz - MvPolynomial.C c₂ * Fy
    let P₂ := MvPolynomial.C c₂ * Fx - MvPolynomial.C c₀ * Fz
    let P₃ := MvPolynomial.C c₀ * Fy - MvPolynomial.C c₁ * Fx
    IsJacobianSyzygy F P₁ P₂ P₃ ∧
    formOfSyzygy P₁ P₂ P₃ =
      (L * Fx - (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₀,
       L * Fy - (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₁,
       L * Fz - (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₂) := by
  have heul := euler_expanded F d hF
  dsimp only [IsJacobianSyzygy, formOfSyzygy]
  refine ⟨by ring, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · linear_combination -MvPolynomial.C c₀ * heul
  · linear_combination -MvPolynomial.C c₁ * heul
  · linear_combination -MvPolynomial.C c₂ * heul

/-- **Theorem 1.3(1) (Algebraic Koszul Rigidity)**: For any homogeneous `F ∈ ℂ[X, Y, Z]` of
degree `d ≥ 2` whose Jacobian partial derivatives `(F_X, F_Y, F_Z)` form a regular sequence
in `ℂ[X, Y, Z]`, every homogeneous degree-`(d - 1)` Jacobian syzygy `(P₁, P₂, P₃)` lies in
the 3-dimensional Koszul subspace and induces a logarithmic pencil form `ω_L = L dF - d F dL`. -/
theorem theorem_1_3_part1_koszul_rigidity (F : MvPolynomial (Fin 3) ℂ) (d : ℕ)
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d)
    (hreg : IsRegularSeq3 (MvPolynomial.pderiv 0 F) (MvPolynomial.pderiv 1 F)
      (MvPolynomial.pderiv 2 F))
    (P₁ P₂ P₃ : MvPolynomial (Fin 3) ℂ)
    (hP₁ : P₁.IsHomogeneous (d - 1)) (hP₂ : P₂.IsHomogeneous (d - 1))
    (hP₃ : P₃.IsHomogeneous (d - 1))
    (hsyz : IsJacobianSyzygy F P₁ P₂ P₃) :
    ∃ c₀ c₁ c₂ : ℂ,
      P₁ = MvPolynomial.C c₁ * MvPolynomial.pderiv 2 F -
           MvPolynomial.C c₂ * MvPolynomial.pderiv 1 F ∧
      P₂ = MvPolynomial.C c₂ * MvPolynomial.pderiv 0 F -
           MvPolynomial.C c₀ * MvPolynomial.pderiv 2 F ∧
      P₃ = MvPolynomial.C c₀ * MvPolynomial.pderiv 1 F -
           MvPolynomial.C c₁ * MvPolynomial.pderiv 0 F ∧
      formOfSyzygy P₁ P₂ P₃ =
        ((MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 +
            MvPolynomial.C c₂ * MvPolynomial.X 2) * MvPolynomial.pderiv 0 F -
          (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₀,
         (MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 +
            MvPolynomial.C c₂ * MvPolynomial.X 2) * MvPolynomial.pderiv 1 F -
          (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₁,
         (MvPolynomial.C c₀ * MvPolynomial.X 0 + MvPolynomial.C c₁ * MvPolynomial.X 1 +
            MvPolynomial.C c₂ * MvPolynomial.X 2) * MvPolynomial.pderiv 2 F -
          (d : MvPolynomial (Fin 3) ℂ) * F * MvPolynomial.C c₂) := by
  set a := MvPolynomial.pderiv 0 F
  set b := MvPolynomial.pderiv 1 F
  set c := MvPolynomial.pderiv 2 F
  have ha_hom : a.IsHomogeneous (d - 1) := isHomogeneous_pderiv F d (by omega) hF 0
  have hb_hom : b.IsHomogeneous (d - 1) := isHomogeneous_pderiv F d (by omega) hF 1
  have hc_hom : c.IsHomogeneous (d - 1) := isHomogeneous_pderiv F d (by omega) hF 2
  have hP3c : P₃ * c = (-P₁) * a + (-P₂) * b := by
    unfold IsJacobianSyzygy at hsyz
    linear_combination hsyz
  obtain ⟨u, v, hP3_eq⟩ := hreg.2.2 P₃ (-P₁) (-P₂) hP3c
  have hP2b : (P₂ + v * c) * b = (-(P₁ + u * c)) * a := by
    unfold IsJacobianSyzygy at hsyz
    linear_combination hsyz - c * hP3_eq
  obtain ⟨w, hP2_tmp⟩ := hreg.2.1 (P₂ + v * c) (-(P₁ + u * c)) hP2b
  have hP2_eq : P₂ = w * a + (-v) * c := by linear_combination hP2_tmp
  have hP1a : (P₁ + w * b + u * c) * a = 0 := by
    unfold IsJacobianSyzygy at hsyz
    linear_combination hsyz - b * hP2_eq - c * hP3_eq
  have hP1_zero : P₁ + w * b + u * c = 0 := hreg.1 _ hP1a
  have hP1_eq : P₁ = (-u) * c + (-w) * b := by linear_combination hP1_zero
  have hP1_c := eq_const_mul_add_const_mul_of_isHomogeneous P₁ c b (-u) (-w) (d - 1)
    hP₁ hc_hom hb_hom hP1_eq
  have hP2_c := eq_const_mul_add_const_mul_of_isHomogeneous P₂ a c w (-v) (d - 1)
    hP₂ ha_hom hc_hom hP2_eq
  have hP3_c := eq_const_mul_add_const_mul_of_isHomogeneous P₃ a b u v (d - 1)
    hP₃ ha_hom hb_hom hP3_eq
  have h1' : P₁ = MvPolynomial.C (-(u.coeff 0)) * c - MvPolynomial.C (w.coeff 0) * b := by
    have hu : (-u).coeff 0 = -(u.coeff 0) := by simp
    have hw : (-w).coeff 0 = -(w.coeff 0) := by simp
    simp only [hu, hw, map_neg] at hP1_c
    rw [map_neg]
    linear_combination hP1_c
  have h2' : P₂ = MvPolynomial.C (w.coeff 0) * a - MvPolynomial.C (v.coeff 0) * c := by
    have hv : (-v).coeff 0 = -(v.coeff 0) := by simp
    simp only [hv, map_neg] at hP2_c
    linear_combination hP2_c
  have h3' : P₃ = MvPolynomial.C (v.coeff 0) * b - MvPolynomial.C (-(u.coeff 0)) * a := by
    rw [map_neg]
    linear_combination hP3_c
  refine ⟨v.coeff 0, -(u.coeff 0), w.coeff 0, h1', h2', h3', ?_⟩
  have hkos := (prop_5_1_koszul_pencil_forms F d hF (v.coeff 0) (-(u.coeff 0)) (w.coeff 0)).2
  rw [h1', h2', h3']
  exact hkos

/-- **Lemma 5.2 (`L_∞` Smoothness)**: Along `L_∞ = {Z = 0}`, the leading form
`X^{m+1} + 2 Y^{m+1}` has no repeated nonzero roots. -/
theorem lemma_5_2_Linf_smooth {m : ℕ} (hm : 2 ≤ m) (X Y : ℂ)
    (h0 : X ^ (m + 1) + 2 * Y ^ (m + 1) = 0)
    (hdx : ((m + 1 : ℕ) : ℂ) * X ^ m = 0) :
    X = 0 ∧ Y = 0 := by
  have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hXm : X ^ m = 0 := (mul_eq_zero.mp hdx).resolve_left hm1
  have hX : X = 0 := by by_contra h; exact pow_ne_zero m h hXm
  subst hX
  rw [zero_pow (by omega), zero_add] at h0
  have hYpow : Y ^ (m + 1) = 0 := (mul_eq_zero.mp h0).resolve_left (by norm_num)
  have hY : Y = 0 := by by_contra h; exact pow_ne_zero (m + 1) h hYpow
  exact ⟨rfl, hY⟩

/-- **Lemma 5.3 (`L_∞` Disjointness)**: `Sing(ℱ_m(λ)) ∩ C_m ∩ L_∞ = ∅` for all `m ≥ 2` and
`λ ≠ 0`. -/
theorem lemma_5_3_Linf_disjoint {m : ℕ} (hm : 2 ≤ m) (lam X Y : ℂ)
    (hlam : lam ≠ 0) (hXY : X ≠ 0 ∨ Y ≠ 0)
    (hC : X ^ (m + 1) + 2 * Y ^ (m + 1) = 0) :
    lam * X ^ (m - 1) * Y ≠ 0 := by
  intro h0
  rcases mul_eq_zero.mp h0 with h1 | hY
  · rcases mul_eq_zero.mp h1 with hlam0 | hXpow
    · exact hlam hlam0
    · have hX : X = 0 := by by_contra h; exact pow_ne_zero (m - 1) h hXpow
      subst hX
      rw [zero_pow (by omega), zero_add] at hC
      have hYpow : Y ^ (m + 1) = 0 := (mul_eq_zero.mp hC).resolve_left (by norm_num)
      have hY : Y = 0 := by by_contra h; exact pow_ne_zero (m + 1) h hYpow
      exact hXY.elim (· rfl) (· hY)
  · subst hY
    rw [zero_pow (by omega), mul_zero, add_zero] at hC
    have hX : X = 0 := by by_contra h; exact pow_ne_zero (m + 1) h hC
    exact hXY.elim (· hX) (· rfl)

/-- **Proposition 5.4 (Parametrization Factorization)**: Along the rational parametrization
`(x(t), y(t))` of `C_m`, both `P_m` and `Q_m` factor explicitly through
`g_m(t; λ) = 2(m + 1)(2 t^{m+1} + 1) - λ t(2t + 1)`. -/
theorem prop_5_4_param_factorization {m : ℕ} (hm : 2 ≤ m) (lam t : ℂ)
    (hden : 1 + 2 * t ^ (m + 1) ≠ 0) :
    PmVec m lam (xParam m t) (yParam m t) =
      -(xParam m t) ^ (m - 1) * (yParam m t - (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ))) *
        (t ^ (m - 1) / (1 + 2 * t ^ (m + 1))) * gmPoly m lam t ∧
    QmVec m lam (xParam m t) (yParam m t) =
      (xParam m t) ^ (m - 2) * (xParam m t + (m : ℂ) / ((m + 1 : ℕ) : ℂ)) *
        (xParam m t / (2 * (1 + 2 * t ^ (m + 1)))) * gmPoly m lam t := by
  have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have htm1 : t ^ m = t ^ (m - 1) * t := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have htm2 : t ^ (m + 1) = t ^ (m - 1) * t ^ 2 := by
    rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
  have hx1 : xParam m t + 1 = t ^ m * (2 * t + 1) / (1 + 2 * t ^ (m + 1)) := by
    unfold xParam
    field_simp [hden]
    rw [pow_succ t m]
    ring
  have hy1 : yParam m t - (1 : ℂ) / 2 = -(2 * t + 1) / (2 * (1 + 2 * t ^ (m + 1))) := by
    unfold yParam xParam
    field_simp [hden]
    rw [pow_succ t m]
    ring
  constructor
  · have hy_pow1 : yParam m t ^ (m - 1) = t ^ (m - 1) * xParam m t ^ (m - 1) := by
      unfold yParam; rw [mul_pow]
    have hy_pow2 : yParam m t ^ m = t ^ (m - 1) * xParam m t ^ (m - 1) * yParam m t := by
      rw [show yParam m t ^ m = yParam m t ^ (m - 1) * yParam m t by
        rw [← pow_succ, show m - 1 + 1 = m by omega], hy_pow1]
    unfold PmVec fmDy gmPoly
    rw [hy_pow1, hy_pow2, hx1, htm1]
    field_simp [hm1, hden]
    rw [hcast]
    ring
  · have hx_pow1 : xParam m t ^ (m - 1) = xParam m t ^ (m - 2) * xParam m t := by
      rw [← pow_succ, show m - 2 + 1 = m - 1 by omega]
    have hx_pow2 : xParam m t ^ m = xParam m t ^ (m - 2) * xParam m t * xParam m t := by
      rw [show xParam m t ^ m = xParam m t ^ (m - 1) * xParam m t by
        rw [← pow_succ, show m - 1 + 1 = m by omega], hx_pow1]
    unfold QmVec fmDx gmPoly
    rw [hx_pow1, hx_pow2, hy1]
    unfold yParam
    field_simp [hm1, hden]
    rw [hcast]
    ring

end LogarithmicRigidity
