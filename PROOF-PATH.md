# Manuscript-to-Lean Correspondence

## Part 1: Unconditional Mathlib-Only Core (`LogarithmicRigidity`, 27 Locked Theorems, 0 Custom Axioms)

| Manuscript Result | Section | Lean Module | Lean Declaration | Axioms |
|---|---|---|---|---|
| Eq. (2.1) Euler identity | §2 | `LogarithmicRigidity/Preliminaries.lean` | `induced_one_form_euler` | Standard 3 only |
| Lemma 2.1 (algebraic criterion) | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_1_tau_ratio_criterion` | Standard 3 only |
| Lemma 2.4 | §2 | `LogarithmicRigidity/Preliminaries.lean` | `lemma_2_4_hBound_mono_superadd` | Standard 3 only |
| Prop. 4.1 (`C¹` first integral) | §4 | `LogarithmicRigidity/RealLogarithmicCalculus.lean` | `prop_4_1_local_first_integral_const` | Standard 3 only |
| Prop. 5.1 (Euler identity) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_1_euler_homogeneous` | Standard 3 only |
| Prop. 5.1(1) (syzygy bijection) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `prop_5_1_syzygy_correspondence` | Standard 3 only |
| Prop. 5.1(3) (Koszul pencils) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `prop_5_1_koszul_pencil_forms` | Standard 3 only |
| Thm. 1.3(1) (Koszul rigidity) | §1, §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `theorem_1_3_part1_koszul_rigidity` | Standard 3 only |
| Lemma 5.2 (parametrization & affine smoothness) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_2_curve_Cm_geometry` | Standard 3 only |
| Lemma 5.2 (`L_∞` smoothness) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `lemma_5_2_Linf_smooth` | Standard 3 only |
| Lemma 5.3 (cofactor & origin) | §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `lemma_5_3_foliation_Fm_cofactor_origin` | Standard 3 only |
| Lemma 5.3 (`L_∞` disjointness) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `lemma_5_3_Linf_disjoint` | Standard 3 only |
| Prop. 5.4 (factorization via `g_m`) | §5 | `LogarithmicRigidity/SyzygyKoszul.lean` | `prop_5_4_param_factorization` | Standard 3 only |
| Prop. 5.4 & Thm. 1.3(2) (linear coeff & countability) | §1, §5 | `LogarithmicRigidity/JacobianSyzygies.lean` | `prop_5_4_and_theorem_1_3_part2` | Standard 3 only |
| Thm. 1.4(1) (arithmetic bounds) | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `hBound_le_rNonZeroBound`, `hBound_add_le_rNonZeroBound` | Standard 3 only |
| Lemma 6.1 (quartic geometry) | §6 | `LogarithmicRigidity/CaseRNonZero.lean` | `lemma_6_1_quartic_geometry` | Standard 3 only |
| Lemma 6.1 (Hessian determinants) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `quartic_hessian_nodes` | Standard 3 only |
| Prop. 6.2 (`L_∞`, elimination, `x=0`) | §6 | `LogarithmicRigidity/Section6ElimCert.lean` | `sing_Linf_empty`, `sing_PQ_elim`, `sing_PQ_x_zero` | Standard 3 only |
| Prop. 6.2 (cofactor & positivity) | §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean` | `prop_6_2_counterexample_nondicritical` | Standard 3 only |
| Prop. 6.2 (no real singularities on `f=0`) | §6, App. A | `LogarithmicRigidity/Section6RealSingFree.lean` | `prop_6_2_no_real_singularity_on_quartic` | Standard 3 only |
| Prop. 6.2 (`q₄` stratum non-dicriticality) | §6, App. A | `LogarithmicRigidity/Section6Q4Cert.lean` | `prop_6_2_q4_stratum_nondicritical` | Standard 3 only |
| Prop. 6.2 (`q₆` stratum & complete affine non-dicriticality) | §6, App. A | `LogarithmicRigidity/Section6Q6Cert.lean` | `prop_6_2_q6_stratum_nondicritical`, `prop_6_2_all_affine_singularities_nondicritical` | Standard 3 only |
| Prop. 6.3 & Thm. 1.4(2) (SOS & FTC Floquet) | §1, §6, App. A | `LogarithmicRigidity/CounterexampleCert.lean`, `Section6ElimCert.lean` | `prop_6_3_and_theorem_1_4_part2`, `floquet_integral_pos_oval1`, `floquet_integral_pos_oval2` | Standard 3 only |

## Part 2: Full Manuscript Theorems (`LogarithmicRigidityConditional`, External Literature Axioms)

| Manuscript Result | Section | Lean Module | Lean Declaration | External Axioms Used |
|---|---|---|---|---|
| Lemma 2.1 (full) | §2 | `LogarithmicRigidityConditional/Section5DegreeMPlusOne.lean` | `lemma_2_1_nondicritical_criterion` | Camacho–Lins Neto–Sad (1984) |
| Lemma 3.1 | §3 | `LogarithmicRigidityConditional/Section3LogarithmicRigidity.lean` | `lemma_3_1_blowup_propagation` | Carnicer (1994), Seidenberg (1968) |
| Proposition 3.2 | §3 | `LogarithmicRigidityConditional/Section3LogarithmicRigidity.lean` | `prop_3_2_logarithmic_residues` | Carnicer (1994), Deligne (1971), Residue Thm. |
| **Theorem 1.1** | §1, §3 | `LogarithmicRigidityConditional/Section3LogarithmicRigidity.lean` | `theorem_1_1_logarithmic_rigidity` | Carnicer (1994), Deligne (1971), Hartogs, Bézout |
| Proposition 4.1 | §4 | `LogarithmicRigidityConditional/Section4RealLogarithmic.lean` | `prop_4_1_real_logarithmic_obstruction` | Giacomini–Llibre–Viano (1996) + IFT |
| **Theorem 1.2** | §1, §4 | `LogarithmicRigidityConditional/Section4RealLogarithmic.lean` | `theorem_1_2_standard_upper_bound`, `theorem_1_2_standard_sharpness` | Thm. 1.1, Prop. 4.1, Carnicer, Harnack (1876), Christopher (2001) |
| **Theorem 1.3(1)** | §1, §5 | `LogarithmicRigidityConditional/Section5DegreeMPlusOne.lean` | `theorem_1_3_part1_smooth_nonexistence` | Dimca (2013) / Serre duality on `ℙ²` |
| **Theorem 1.3(2)** | §1, §5 | `LogarithmicRigidityConditional/Section5DegreeMPlusOne.lean` | `theorem_1_3_part2_existence` | Analytic IFT & Identity Thm. |
| **Theorem 1.4(1)** | §1, §6 | `LogarithmicRigidityConditional/Section6CaseRNonZero.lean` | `theorem_1_4_part1_r_nonzero_bounds` | Thm. 1.1, Prop. 4.1, Carnicer, Harnack, Dimca |
| **Theorem 1.4(2)** | §1, §6 | `LogarithmicRigidityConditional/Section6CaseRNonZero.lean` | `theorem_1_4_part2_counterexample` | Standard 3 only (re-exports unconditional core) |
