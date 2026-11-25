# External-Axiom Register

## 1. Unconditional Core (`LogarithmicRigidity`)
Every theorem in `LogarithmicRigidity/*` and `comparator/Challenge.lean` declares **zero** custom `axiom` statements and depends exclusively on Mathlib `v4.35.0` and `[propext, Classical.choice, Quot.sound]`.

## 2. External Literature Axioms (`LogarithmicRigidityConditional/ExternalLiterature.lean`)
To formalize the full geometric statements of Theorems 1.1, 1.2, 1.3, and 1.4 without axiomatizing any result the manuscript itself proves, `LogarithmicRigidityConditional/ExternalLiterature.lean` declares only the following established peer-reviewed external theorems absent from Mathlib `v4.35.0`. Every axiom is formulated over opaque geometric predicates (never over universally quantified arbitrary `Prop` or `ℕ` parameters) so the axiom set admits an explicit consistent model.

| # | Lean Axiom | Published Peer-Reviewed Source | Used By |
|---|---|---|---|
| 1 | `carnicer_local_inequality` | M. M. Carnicer (1994), *Ann. of Math.* **140**, 289–294, Thm. 1 (Prop. 2.2) | `lemma_3_1_blowup_propagation` |
| 2 | `carnicer_degree_bound` | M. M. Carnicer (1994), *Ann. of Math.* **140**, 289–294, Main Thm. (Prop. 2.2) | `theorem_1_2_standard_upper_bound`, `theorem_1_4_part1_r_nonzero_bounds` |
| 3 | `deligne_logarithmic_closed` | P. Deligne (1971), *Théorie de Hodge. II*, Publ. Math. IHÉS **40**, Cor. 3.2.14 (Prop. 2.3) | `prop_3_2_logarithmic_residues` |
| 4 | `residue_theorem_CP1` | Classical Residue Theorem on `ℂℙ¹` & compact Riemann surface holomorphic functions | `prop_3_2_logarithmic_residues` |
| 5 | `hartogs_and_no_holomorphic_1forms_CP2` | Hartogs' extension theorem & `H⁰(ℂℙ², Ω¹_{ℂℙ²}) = 0` | `theorem_1_1_logarithmic_rigidity` |
| 6 | `bezout_rational_first_integral_dicritical`, `logarithmic_two_component_gives_first_integral` | Bézout's theorem on `ℂℙ²` (intersection of two plane curves & dicriticality of rational first integrals) | `theorem_1_1_logarithmic_rigidity` |
| 7 | `embedded_log_resolution_exists`, `log_order_nonneg_implies_logarithmic` | A. Seidenberg (1968), *Amer. J. Math.* **90**, 248–269 & embedded resolution of plane curve singularities | `lemma_3_1_blowup_propagation`, `prop_3_2_logarithmic_residues`, `theorem_1_1_logarithmic_rigidity` |
| 8 | `glv_and_ift_no_purely_real_logarithmic_limit_cycle` | H. Giacomini, J. Llibre, M. Viano (1996), *Nonlinearity* **9**, 501–516 + Implicit Function Theorem | `prop_4_1_real_logarithmic_obstruction` |
| 9 | `harnack_total_oval_bound`, `harnack_singular_irred_bound` | C. G. A. Harnack (1876), *Math. Ann.* **10**, 189–199 + normalization genus–`δ` formula | `theorem_1_2_standard_upper_bound`, `theorem_1_4_part1_r_nonzero_bounds` |
| 10 | `christopher_sharpness_construction` | C. Christopher (2001), *Geom. Dedicata* **88**, 255–258 + Harnack M-curve existence | `theorem_1_2_standard_sharpness` |
| 11 | `camacho_lins_neto_sad_nondicritical` | C. Camacho, A. Lins Neto, P. Sad (1984), *J. Differential Geom.* **20**, 143–174 | `lemma_2_1_nondicritical_criterion` |
| 12 | `dimca_serre_duality_syzygy_defect` | A. Dimca (2013), *Bull. Math. Soc. Sci. Math. Roumanie* **56(104)**, Thm. 3.1 & Serre duality on `ℙ²` | `theorem_1_3_part1_smooth_nonexistence`, `theorem_1_4_part1_r_nonzero_bounds` |
| 13 | `analytic_perturbation_countable_resonances` | Analytic Implicit Function Theorem & Identity Theorem for holomorphic functions | `theorem_1_3_part2_existence` |
