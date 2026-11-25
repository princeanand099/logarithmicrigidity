# Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations

Lean 4 (`v4.35.0`, Mathlib `v4.35.0`) formalization of Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations*.

## Architecture & Scope

The repository is split into two strictly separated libraries:

1. **`LogarithmicRigidity` (Unconditional Mathlib-Only Core — 0 custom axioms)**
   Every declaration in `LogarithmicRigidity/*` and `comparator/Challenge.lean` (27 locked theorems) depends exclusively on Mathlib `v4.35.0` and `[propext, Classical.choice, Quot.sound]`:
   - **§2**: Eq. (2.1) Euler identity (`induced_one_form_euler`), Lemma 2.1 algebraic criterion (`lemma_2_1_tau_ratio_criterion`), Lemma 2.4 (`lemma_2_4_hBound_mono_superadd`).
   - **§4**: Prop. 4.1 `C¹` local first-integral invariance (`prop_4_1_local_first_integral_const`).
   - **§5**: Prop. 5.1 Euler identity (`prop_5_1_euler_homogeneous`), Prop. 5.1(1) syzygy bijection (`prop_5_1_syzygy_correspondence`), Prop. 5.1(3) Koszul pencil forms (`prop_5_1_koszul_pencil_forms`), Thm. 1.3(1) algebraic Koszul rigidity (`theorem_1_3_part1_koszul_rigidity`), Lemma 5.2 (`lemma_5_2_curve_Cm_geometry`, `lemma_5_2_Linf_smooth`), Lemma 5.3 (`lemma_5_3_foliation_Fm_cofactor_origin`, `lemma_5_3_Linf_disjoint`), Prop. 5.4 (`prop_5_4_param_factorization`, `prop_5_4_and_theorem_1_3_part2`).
   - **§6 & Appendix A**: Thm. 1.4(1) arithmetic inequalities (`hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound`), Lemma 6.1 (`lemma_6_1_quartic_geometry`, `quartic_hessian_nodes`), Prop. 6.2 (`sing_Linf_empty`, `sing_PQ_elim`, `sing_PQ_x_zero`, `prop_6_2_counterexample_nondicritical`, `prop_6_2_no_real_singularity_on_quartic`, `prop_6_2_q4_stratum_nondicritical`, `prop_6_2_q6_stratum_nondicritical`, `prop_6_2_all_affine_singularities_nondicritical`), Prop. 6.3 & Thm. 1.4(2) (`prop_6_3_and_theorem_1_4_part2`, `floquet_integral_pos_oval1`, `floquet_integral_pos_oval2`).

2. **`LogarithmicRigidityConditional` (Full Manuscript Formalization on External Literature Axioms)**
   Formalizes every theorem, proposition, and lemma of the manuscript—including **Lemma 2.1 (full)**, **Lemma 3.1**, **Proposition 3.2**, **Theorem 1.1**, **Proposition 4.1**, **Theorem 1.2 (upper bound & sharpness)**, **Theorem 1.3(1)–(2)**, and **Theorem 1.4(1)–(2)**—on top of `LogarithmicRigidity` and the minimal, sound, exact peer-reviewed external literature axioms isolated in `LogarithmicRigidityConditional/ExternalLiterature.lean` and documented in `EXTERNAL-AXIOMS.md`. Zero manuscript-owned results are axiomatized.

## Build & Verification

```bash
lake exe cache get
lake build LogarithmicRigidity LogarithmicRigidityConditional Solution
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake env lean LogarithmicRigidityConditional/AuditConditionalAxioms.lean
lake comparator
```
