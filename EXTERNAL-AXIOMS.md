# External-Axiom Register

## 1. Unconditional Core (`LogarithmicRigidity`)
Every theorem in `LogarithmicRigidity/*` and `comparator/Challenge.lean` (37 locked theorems) declares **zero** custom `axiom` statements and depends exclusively on Mathlib `v4.35.0` and `[propext, Classical.choice, Quot.sound]`.

## 2. External Literature Axioms (`LogarithmicRigidityConditional/ExternalLiterature.lean`)
Because complex projective algebraic geometry (embedded log-resolutions, Deligne's Hodge II closedness, Carnicer's non-dicritical multiplicity theorem, Hartogs' extension, Bézout's theorem, Harnack's oval bound, planar limit-cycle theory, and Dimca's syzygy-defect formula) is not yet in Mathlib `v4.35.0`, `LogarithmicRigidityConditional/ExternalLiterature.lean` declares abstract interfaces and external peer-reviewed literature axioms. Every manuscript-owned deduction (Proposition 4.1's `C¹` constancy via `prop_4_1_local_first_integral_const`, Theorem 1.3(1)'s deduction from Dimca's defect formula + Koszul dicriticality, Theorem 1.4(1)'s `m = 3` Tjurina and real-cusp `A₂` deduction, and Lemma 3.1's signed `ℤ`-order propagation) is proved in Lean rather than axiomatized.

| # | Lean Axiom | Published Peer-Reviewed Source | Used By |
|---|---|---|---|
| 1 | `carnicer_local_inequality` | M. M. Carnicer (1994), *Ann. of Math.* **140**, 289–294, Thm. 1 (Prop. 2.2) | `lemma_3_1_blowup_propagation` |
| 2 | `carnicer_degree_bound` | M. M. Carnicer (1994), *Ann. of Math.* **140**, 289–294, Main Thm. (Prop. 2.2) | `theorem_1_2_standard_upper_bound`, `theorem_1_4_part1_r_nonzero_bounds` |
| 3 | `deligne_logarithmic_closed` | P. Deligne (1971), *Théorie de Hodge. II*, Publ. Math. IHÉS **40**, Cor. 3.2.14 (Prop. 2.3) | `prop_3_2_logarithmic_residues` |
| 4 | `residue_theorem_CP1` | Classical Residue Theorem on `ℂℙ¹` & compact Riemann surface holomorphic functions | `prop_3_2_logarithmic_residues` |
| 5 | `hartogs_and_no_holomorphic_1forms_CP2` | Hartogs' extension theorem & `H⁰(ℂℙ², Ω¹_{ℂℙ²}) = 0` | `theorem_1_1_logarithmic_rigidity` |
| 6 | `bezout_rational_first_integral_dicritical`, `logarithmic_two_component_gives_first_integral` | Bézout's theorem on `ℂℙ²` (intersection of two plane curves & dicriticality of rational first integrals) | `theorem_1_1_logarithmic_rigidity` |
| 7 | `embedded_log_resolution_exists`, `log_order_nonneg_implies_logarithmic` | A. Seidenberg (1968), *Amer. J. Math.* **90**, 248–269 & embedded resolution of plane curve singularities | `lemma_3_1_blowup_propagation`, `prop_3_2_logarithmic_residues`, `theorem_1_1_logarithmic_rigidity` |
| 8 | `giacomini_llibre_viano_limit_cycle_orbit`, `ift_local_first_integral_contradicts_isolation` | H. Giacomini, J. Llibre, M. Viano (1996), *Nonlinearity* **9**, 501–516 + Implicit Function Theorem | `prop_4_1_real_logarithmic_obstruction` (combined with unconditional `prop_4_1_local_first_integral_const`) |
| 9 | `harnack_total_oval_bound`, `harnack_singular_irred_bound`, `plane_curve_delta_one_cusp_classification` | C. G. A. Harnack (1876), *Math. Ann.* **10**, 189–199 + normalization genus–`δ` formula + classical `δ = 1` plane singularity classification (`A₁`/`A₂`) | `theorem_1_2_standard_upper_bound`, `theorem_1_4_part1_r_nonzero_bounds` |
| 10 | `christopher_sharpness_construction` | C. Christopher (2001), *Geom. Dedicata* **88**, 255–258 + Harnack M-curve existence (`m ≥ 2`) & linear saddle (`m = 1`) | `theorem_1_2_standard_sharpness` |
| 11 | `camacho_lins_neto_sad_nondicritical` | C. Camacho, A. Lins Neto, P. Sad (1984), *J. Differential Geom.* **20**, 143–174 | `lemma_2_1_nondicritical_criterion` |
| 12 | `dimca_syzygy_defect_formula`, `koszul_subspace_dicritical` | A. Dimca (2013), *Bull. Math. Soc. Sci. Math. Roumanie* **56(104)**, Thm. 3.1 + Koszul pencil dicriticality (Bézout) | `theorem_1_3_part1_smooth_nonexistence`, `lemma_m3_nondicritical_delta_tau` |
| 13 | `analytic_perturbation_countable_resonances` | Analytic Implicit Function Theorem & Identity Theorem for holomorphic functions (with `E` linked to `IsSmoothSingNonDicriticalOnCm`) | `theorem_1_3_part2_existence` |
