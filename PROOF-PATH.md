# Manuscript-to-Lean Correspondence (100% Unconditional Mathlib-Only)

Every declaration listed below is proved **100% unconditionally on top of Mathlib `v4.35.0`** and `[propext, Classical.choice, Quot.sound]`, with zero custom axioms and zero hypothesis-bundle shortcuts.

| Manuscript Result | Section | Lean Module | Lean Declaration | Status |
|---|---|---|---|---|
| Eq. (2.1) Euler identity | §2 | `LogarithmicRigidity/Preliminaries.lean` | `induced_one_form_euler` | Proved (Unconditional) |
| Lemma 2.1 | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_1_tau_ratio_criterion` | Proved (Unconditional) |
| Lemma 2.4 | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_4_hBound_mono_superadd` | Proved (Unconditional) |
| Prop. 4.1 (`C¹` first integral) | §4 | `LogarithmicRigidity/RealLogarithmicCalculus.lean` | `prop_4_1_local_first_integral_const` | Proved (Unconditional) |
| Prop. 5.1 (Euler identity) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_1_euler_homogeneous` | Proved (Unconditional) |
| Lemma 5.2 | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_2_curve_Cm_geometry` | Proved (Unconditional) |
| Lemma 5.3 | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_3_foliation_Fm_cofactor_origin` | Proved (Unconditional) |
| Prop. 5.4 & Thm 1.3(2) | §1, §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_4_and_theorem_1_3_part2` | Proved (Unconditional) |
| Thm 1.4(1) arithmetic bounds | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound` | Proved (Unconditional) |
| Lemma 6.1 | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `lemma_6_1_quartic_geometry` | Proved (Unconditional) |
| Lemma 6.1 (Hessians) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `quartic_hessian_nodes` | Proved (Unconditional) |
| Prop. 6.2 (`L_∞`) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_Linf_empty` | Proved (Unconditional) |
| Prop. 6.2 (Elimination) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_PQ_elim` | Proved (Unconditional) |
| Prop. 6.2 (`x = 0` stratum) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_PQ_x_zero` | Proved (Unconditional) |
| Prop. 6.2 (Cofactor & SOS) | §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_2_counterexample_nondicritical` | Proved (Unconditional) |
| Prop. 6.3 & Thm 1.4(2) (SOS) | §1, §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_3_and_theorem_1_4_part2` | Proved (Unconditional) |
| Prop. 6.3 (FTC Floquet) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `floquet_integral_pos_oval1`, `floquet_integral_pos_oval2` | Proved (Unconditional) |

## Not Formalized (Missing Mathlib `v4.35.0` Foundations)

The following full geometric theorems are **not** formalized (and are intentionally omitted rather than faked via hypothesis structures):
- **Theorem 1.1** (requires Deligne 1971 *Théorie de Hodge II* + Carnicer 1994 Seidenberg/Camacho–Sad).
- **Theorem 1.2** (requires Theorem 1.1 + Harnack 1876 + Giacomini–Llibre–Viano 1996 + Christopher 2001).
- **Theorem 1.3(1)** (requires Dimca 2013 / Serre duality & coherent sheaf cohomology on $\mathbb{P}^2$).
- **Theorem 1.4(1)** in full geometric generality (requires Theorem 1.1 + Theorem 1.3(1) + Harnack 1876).
