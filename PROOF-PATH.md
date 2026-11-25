# Manuscript-to-Lean Correspondence

All declarations listed in the table below are proved on top of Mathlib `v4.35.0` using only `[propext, Classical.choice, Quot.sound]`, with no custom axioms and no hypothesis-bundle wrappers.

| Manuscript Result | Section | Lean Module | Lean Declaration | Status |
|---|---|---|---|---|
| Eq. (2.1) Euler identity | §2 | `LogarithmicRigidity/Preliminaries.lean` | `induced_one_form_euler` | Proved |
| Lemma 2.1 (algebraic criterion) | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_1_tau_ratio_criterion` | Proved |
| Lemma 2.4 | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_4_hBound_mono_superadd` | Proved |
| Prop. 4.1 (`C¹` first integral) | §4 | `LogarithmicRigidity/RealLogarithmicCalculus.lean` | `prop_4_1_local_first_integral_const` | Proved |
| Prop. 5.1 (Euler identity) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_1_euler_homogeneous` | Proved |
| Prop. 5.1(1) (syzygy bijection) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `prop_5_1_syzygy_correspondence` | Proved |
| Prop. 5.1(3) (Koszul pencils) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `prop_5_1_koszul_pencil_forms` | Proved |
| Thm. 1.3(1) (Koszul rigidity) | §1, §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `theorem_1_3_part1_koszul_rigidity` | Proved (algebraic core) |
| Lemma 5.2 (parametrization & affine smoothness) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_2_curve_Cm_geometry` | Proved |
| Lemma 5.2 (`L_∞` smoothness) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `lemma_5_2_Linf_smooth` | Proved |
| Lemma 5.3 (cofactor & origin) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_3_foliation_Fm_cofactor_origin` | Proved |
| Lemma 5.3 (`L_∞` disjointness) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `lemma_5_3_Linf_disjoint` | Proved |
| Prop. 5.4 (factorization via `g_m`) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `prop_5_4_param_factorization` | Proved |
| Prop. 5.4 & Thm. 1.3(2) (linear coeff & countability) | §1, §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_4_and_theorem_1_3_part2` | Proved (algebraic/set core) |
| Thm. 1.4(1) (arithmetic bounds) | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound` | Proved (arithmetic core) |
| Lemma 6.1 (quartic geometry) | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `lemma_6_1_quartic_geometry` | Proved |
| Lemma 6.1 (Hessian determinants) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `quartic_hessian_nodes` | Proved |
| Prop. 6.2 (`L_∞`) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_Linf_empty` | Proved |
| Prop. 6.2 (elimination) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_PQ_elim` | Proved |
| Prop. 6.2 (`x = 0` stratum) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_PQ_x_zero` | Proved |
| Prop. 6.2 (cofactor & positivity) | §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_2_counterexample_nondicritical` | Proved |
| Prop. 6.3 & Thm. 1.4(2) (SOS) | §1, §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_3_and_theorem_1_4_part2` | Proved |
| Prop. 6.3 (FTC Floquet integrals) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `floquet_integral_pos_oval1`, `floquet_integral_pos_oval2` | Proved |

## Not Formalized

- **Theorem 1.1** (requires Deligne 1971 *Théorie de Hodge II* + Carnicer 1994 / Seidenberg / Camacho–Sad).
- **Theorem 1.2** (requires Theorem 1.1 + Harnack 1876 + Giacomini–Llibre–Viano 1996 + Christopher 2001).
- **Theorem 1.3(1)** full geometric statement (requires Nullstellensatz + Bézout + analytic dicriticality; algebraic Koszul rigidity is proved in `theorem_1_3_part1_koszul_rigidity`).
- **Theorem 1.4(1)** full geometric statement (requires Theorem 1.1 + Proposition 5.1(2) Serre duality on `ℙ²` + Harnack 1876).
