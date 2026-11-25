# Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations

Lean 4 (`v4.35.0`, Mathlib `v4.35.0`) formalization of Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations*.

## Architecture & Scope

The repository is split into two strictly separated libraries:

1. **`LogarithmicRigidity` (Unconditional Mathlib-Only Core — 37 Locked Theorems, 0 Custom Axioms)**
   Every declaration in `LogarithmicRigidity/*` and `comparator/Challenge.lean` (37 locked theorems) depends exclusively on Mathlib `v4.35.0` and `[propext, Classical.choice, Quot.sound]`:
   - **§2**: Eq. (2.1) Euler identity (`induced_one_form_euler`), Lemma 2.1 algebraic criterion (`lemma_2_1_tau_ratio_criterion`), Lemma 2.4 (`lemma_2_4_hBound_mono_superadd`).
   - **§4**: Prop. 4.1 `C¹` local first-integral invariance (`prop_4_1_local_first_integral_const`).
   - **§5**: Prop. 5.1 Euler identity (`prop_5_1_euler_homogeneous`), Euler kernel surjectivity (`prop_5_1_euler_kernel_surj`), syzygy bijection (`prop_5_1_syzygy_correspondence`), Koszul pencil forms (`prop_5_1_koszul_pencil_forms`), Thm. 1.3(1) regular-sequence Koszul rigidity (`theorem_1_3_part1_koszul_rigidity`), Lemma 5.2 (`lemma_5_2_curve_Cm_geometry`, `lemma_5_2_Linf_smooth`, `lemma_5_2_param_surjective`, `lemma_5_2_Fm_no_common_root_Linf`), Lemma 5.3 (`lemma_5_3_foliation_Fm_cofactor_origin`, `lemma_5_3_Linf_disjoint`, `lemma_5_3_Pm_Qm_coprime`, `lemma_5_3_blowup_origin`), Prop. 5.4 (`prop_5_4_param_factorization`, `prop_5_4_div_and_asymp`, `prop_5_4_and_theorem_1_3_part2`).
   - **§6 & Appendix A**: Thm. 1.4(1) arithmetic inequalities (`hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound`), Lemma 6.1 (`lemma_6_1_quartic_geometry`, `quartic_Linf_smooth`, `quartic_real_compact`, `quartic_real_smooth_and_sign`, `quartic_hessian_nodes`), Prop. 6.2 (`sing_Linf_empty` via exact `InducedOneForm`, `counterexample_saturation_cert`, `sing_PQ_elim`, `sing_PQ_x_zero`, `prop_6_2_counterexample_nondicritical`, `prop_6_2_no_real_singularity_on_quartic`, `prop_6_2_q4_stratum_nondicritical`, `prop_6_2_q6_stratum_nondicritical`, `prop_6_2_all_affine_singularities_nondicritical`), Prop. 6.3 & Thm. 1.4(2) (`prop_6_3_and_theorem_1_4_part2`, `floquet_integral_pos_oval1`, `floquet_integral_pos_oval2`).

2. **`LogarithmicRigidityConditional` (Conditional Full-Manuscript Synthesis on External Literature Axioms)**
   Formalizes the logical architecture of **Lemma 2.1 (full)**, **Lemma 3.1** (signed `ℤ`-order blow-up propagation), **Proposition 3.2**, **Theorem 1.1**, **Proposition 4.1** (directly invoking `prop_4_1_local_first_integral_const`), **Theorem 1.2 (upper bound & sharpness for all `m ≥ 1`)**, **Theorem 1.3(1)–(2)** (with Dimca's defect formula separated from Koszul dicriticality, and `E` linked to `IsSmoothSingNonDicriticalOnCm`), and **Theorem 1.4(1)–(2)** (with the `m = 3` real-cusp `A₂` step proved from `lemma_m3_nondicritical_delta_tau`, `plane_curve_delta_one_cusp_classification`, and `harnack_singular_irred_bound`), over the external literature axioms isolated in `LogarithmicRigidityConditional/ExternalLiterature.lean` and documented in `EXTERNAL-AXIOMS.md`.

## Build & Verification

```bash
lake exe cache get
lake build LogarithmicRigidity LogarithmicRigidityConditional Solution
lake env lean LogarithmicRigidity/AuditAxioms.lean
lake env lean LogarithmicRigidityConditional/AuditConditionalAxioms.lean
lake comparator
```
