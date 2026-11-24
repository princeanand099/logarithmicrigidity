# Manuscript-to-Lean Correspondence and Dependency DAG

Every substantive theorem, proposition, and lemma in Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of Non-Dicritical Foliations*, is formalized with zero `sorry`s and zero custom axioms.

| Manuscript Result | Section | Lean Module | Lean Declaration | Status |
|---|---|---|---|---|
| Eq. (2.1) Euler identity | §2 | `LogarithmicRigidity/Preliminaries.lean` | `induced_one_form_euler` | Proved (CI verified) |
| Lemma 2.1 | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_1_tau_ratio_criterion` | Proved (CI verified) |
| Lemma 2.4 | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_4_hBound_mono_superadd` | Proved (CI verified) |
| Lemma 3.1 | §3 | `LogarithmicRigidity/LogarithmicRigidity.lean` | `lemma_3_1_blowup_propagation` | Proved (CI verified) |
| Proposition 3.2 | §3 | `LogarithmicRigidity/LogarithmicRigidity.lean` | `prop_3_2_logarithmic_residues` | Proved (CI verified) |
| Theorem 1.1 | §1, §3 | `LogarithmicRigidity/LogarithmicRigidity.lean` | `theorem_1_1_logarithmic_rigidity` | Proved (CI verified) |
| Proposition 4.1 | §4 | `LogarithmicRigidity/RealLogarithmic.lean` | `prop_4_1_real_logarithmic_obstruction` | Proved (CI verified) |
| Theorem 1.2 | §1, §4 | `LogarithmicRigidity/RealLogarithmic.lean` | `theorem_1_2_standard_bound_sharp` | Proved (CI verified) |
| Proposition 5.1 | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_1_jacobian_syzygy` | Proved (CI verified) |
| Theorem 1.3(1) | §1, §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `theorem_1_3_part1_smooth_nonexistence` | Proved (CI verified) |
| Lemma 5.2 | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_2_curve_Cm_geometry` | Proved (CI verified) |
| Lemma 5.3 | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_3_foliation_Fm_cofactor_origin` | Proved (CI verified) |
| Prop. 5.4 & Thm 1.3(2) | §1, §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_4_and_theorem_1_3_part2` | Proved (CI verified) |
| Theorem 1.4(1) | §1, §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `theorem_1_4_part1_r_nonzero_bounds` | Proved (CI verified) |
| Lemma 6.1 | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `lemma_6_1_quartic_geometry` | Proved (CI verified) |
| Proposition 6.2 | §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_2_counterexample_nondicritical` | Proved (CI verified) |
| Prop. 6.3 & Thm 1.4(2) | §1, §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_3_and_theorem_1_4_part2` | Proved (CI verified) |
