# Formalization Progress Tracker

## Current Status
- **Toolchain:** Lean `v4.35.0`, Mathlib `v4.35.0`, `comparator` `v4.35.0`
- **Build Status:** CI verified (`LAKE_BUILD_EXIT=0` at commit `9d6408b27ecda04d14089c8baccdda0c31d999a0`, 9068 jobs)
- **Unconditional Core (`LogarithmicRigidity`):** 37 locked theorems, 0 `sorry`, 0 custom axioms (`[propext, Classical.choice, Quot.sound]` only)
- **Conditional Full-Manuscript Synthesis (`LogarithmicRigidityConditional`):** 12 headline theorems covering Lemma 2.1, Lemma 3.1, Prop. 3.2, Theorem 1.1, Prop. 4.1, Theorem 1.2 (upper bound & sharpness for all `m ≥ 1`), Theorem 1.3(1)–(2), `lemma_m3_nondicritical_delta_tau`, and Theorem 1.4(1)–(2)

## Audit Remediation Completed (2026-11-25)
1. **Fixed `sing_Linf_empty` formula defect:** Replaced the hand-written `L_∞` polynomial (which had omitted `+ 8 * Y ^ 3` and included stray degree-4 terms) with the exact `InducedOneForm` restriction `counterexampleLinfForm` from Eq. (2.1).
2. **Closed unconditional Section 6 geometry, compactness, and saturation gaps (`LogarithmicRigidity/Section6GeometryCert.lean`):**
   - `quartic_Linf_smooth`: smoothness of `F_4(X, Y) = 2(X⁴ - X² Y² + Y⁴)` along `L_∞`.
   - `quartic_real_pos_of_large` & `quartic_real_compact`: unconditional `IsCompact` proof for `C(ℝ)`.
   - `quartic_real_smooth_and_sign`: real smoothness (`∇f ≠ 0` on `C(ℝ)`) and sign witnesses `f(-1, 0) < 0`, `f(1, 0) < 0`.
   - `counterexample_saturation_cert`: saturation/coprimality certificate (`gcd(P, Q) = 1` and `Z ∤ A`).
3. **Closed unconditional Section 5 algebraic, blow-up, and asymptotic gaps (`LogarithmicRigidity/Section5Completeness.lean`):**
   - `prop_5_1_euler_kernel_surj`: Euler kernel surjectivity in `ℂ[X, Y, Z]³` via `IsRegularSeq3 (X 0) (X 1) (X 2)`.
   - `lemma_5_2_param_surjective` & `lemma_5_2_Fm_no_common_root_Linf`: birational surjectivity and coprimality core of irreducibility of `F_m`.
   - `lemma_5_3_Pm_Qm_coprime` & `lemma_5_3_blowup_origin`: saturation witnesses and exact blow-up chart identities in both `y = u x` and `x = v y` (fixing the `(v + 2)` chart coefficient) plus exact eigenvalue ratio `μ₁(ζ)/μ₂(ζ) = -1/m + λ ζ / (2 m (m + 1))`.
   - `prop_5_4_div_and_asymp`: exact formulas for `div(𝒴_m)(x, w x)` and `K̃_m(x, w x)` directly linked to `rhoLinearCoeff m ω`.
4. **Eliminated manuscript-owned axioms in `LogarithmicRigidityConditional`:**
   - **Proposition 4.1:** Replaced monolithic axiom with GLV (1996) + IFT and directly invoked the unconditional `LogarithmicRigidity.prop_4_1_local_first_integral_const`.
   - **Theorem 1.3(1) & `m = 3` Tjurina bound:** Separated Dimca (2013) defect formula (`dimca_syzygy_defect_formula`) from Koszul pencil dicriticality (`koszul_subspace_dicritical`), proving both `theorem_1_3_part1_smooth_nonexistence` and `lemma_m3_nondicritical_delta_tau` in Lean.
   - **Theorem 1.3(2):** Linked `E` in `analytic_perturbation_countable_resonances` to `IsSmoothSingNonDicriticalOnCm m lam`.
   - **Theorem 1.4(1) Case 4 (`m = 3`):** Removed the baked-in `m = 3` cusp conclusion from Harnack's axiom and proved it from `lemma_m3_nondicritical_delta_tau`, `plane_curve_delta_one_cusp_classification`, and `harnack_singular_irred_bound`.
   - **Theorem 1.2 Sharpness:** Extended from `m ≥ 2` to all `m ≥ 1`.
   - **Lemma 3.1:** Switched `cumulativeOrder` from saturating `ℕ` to signed `ℤ` via structural recursion on `ℕ`.
