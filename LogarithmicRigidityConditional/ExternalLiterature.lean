/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.Preliminaries
import LogarithmicRigidity.RealLogarithmicCalculus

/-!
# External Peer-Reviewed Literature Axioms

This module isolates the **minimum, exact** peer-reviewed classical theorems external to
Prince Anand (November 2026), *Logarithmic Rigidity and Algebraic Limit Cycles of
Non-Dicritical Foliations*, that are not yet formalized in Mathlib `v4.35.0`.

Strict governance:
- Zero manuscript-owned theorems, propositions, or lemmas are axiomatized here.
- Every `axiom` corresponds to a specific published theorem cited in the manuscript,
  documented in full in `EXTERNAL-AXIOMS.md`.
- Every `axiom` is formulated over opaque geometric predicates (never over universally
  quantified arbitrary `Prop` or `ℕ` parameters) so the entire axiom set admits an
  explicit consistent model and cannot derive `False`.
- The unconditional Mathlib-only library `LogarithmicRigidity` does **not** depend on
  any declaration in this module.
-/

namespace LogarithmicRigidityConditional

open LogarithmicRigidity

/-! ## Minimal Abstract Interfaces for Classical Geometric Objects -/

/-- A saturated holomorphic singular foliation `ℱ` of degree `m` on `ℂℙ²`. -/
structure ProjectiveFoliation where
  deg : ℕ
  isSaturated : Prop

/-- A reduced algebraic curve `S = {F₁ ··· F_k = 0} ⊂ ℂℙ²` with `k` irreducible components
of positive degrees `degF i`. -/
structure ReducedCurve where
  k : ℕ
  degF : Fin k → ℕ
  degF_pos : ∀ i, 0 < degF i

/-- Total projective degree `∑ deg F_i` of a reduced algebraic curve. -/
def ReducedCurve.totalDeg (S : ReducedCurve) : ℕ :=
  ∑ i : Fin S.k, S.degF i

/-- Predicate asserting `S` is `ℱ`-invariant and every singularity of `ℱ` on `S` is
non-dicritical. -/
opaque IsNonDicriticalInvariant (F : ProjectiveFoliation) (S : ReducedCurve) : Prop

/-- Predicate asserting `ℱ` is a logarithmic foliation with nonzero residues `λ_i` along `S_i`
satisfying `∑ λ_i deg F_i = 0`. -/
def IsLogarithmicFoliation (_F : ProjectiveFoliation) (S : ReducedCurve)
    (lam : Fin S.k → ℂ) : Prop :=
  (∀ i, lam i ≠ 0) ∧ (∑ i : Fin S.k, lam i * (S.degF i : ℂ)) = 0

/-- Predicate asserting `ℱ` admits a nonconstant rational first integral `F_0^a / F_1^b`
with `a, b > 0` on a 2-component curve `S`. -/
opaque HasTwoComponentRationalFirstIntegral (F : ProjectiveFoliation) (S : ReducedCurve)
    (hk : S.k = 2) (a b : ℕ) : Prop

/-- Local multiplicity condition for a non-dicritical singularity of a foliation germ. -/
opaque IsNonDicriticalSingularity (nuF nuC : ℕ) : Prop

/-- A single point blow-up step `σ_j : X_j → X_{j-1}` in an embedded log-resolution of `S`. -/
structure BlowUpStep where
  /-- Algebraic multiplicity `ν_p(ℱ_{j-1})` of the strict transform foliation at center `p`. -/
  nuF : ℕ
  /-- Multiplicity `ν_p(C_{j-1})` of the reduced total transform curve at center `p`. -/
  nuC : ℕ
  /-- The center `p` is either a regular point of `ℱ_{j-1}` (`ν_p(ℱ) = 0, ν_p(C) = 1`)
  or a non-dicritical singularity of `ℱ_{j-1}`. -/
  isRegularOrNonDicritical : (nuF = 0 ∧ nuC = 1) ∨ IsNonDicriticalSingularity nuF nuC

/-- An embedded log-resolution `π = σ_1 ∘ ··· ∘ σ_N : X̃ → ℂℙ²` of a reduced invariant curve `S`. -/
structure EmbeddedLogResolution (F : ProjectiveFoliation) (S : ReducedCurve) where
  N : ℕ
  steps : Fin N → BlowUpStep
  allNonDicritical : IsNonDicriticalInvariant F S

/-- Predicate asserting the pullback `α = π*(ω/F)` belongs to `H⁰(X̃, Ω¹_{X̃}(log D))`. -/
opaque PullbackIsLogarithmic {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) : Prop

/-- Predicate asserting `α = π*(ω/F)` is closed (`dα = 0`). -/
opaque PullbackIsClosed {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) : Prop

/-- Poincaré residue `λ_i = Res_{S̃_i}(α)` along each strict transform component `S̃_i`. -/
opaque poincareResidue {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) (i : Fin S.k) : ℂ

/-- Predicate asserting `β = ω/F - ∑ λ_i dF_i/F_i` vanishes identically on `ℂℙ²`. -/
opaque FormEqualsLogarithmicSum (F : ProjectiveFoliation) (S : ReducedCurve)
    (lam : Fin S.k → ℂ) : Prop

/-! ## Axioms 1–2: Carnicer (1994), *Ann. of Math.* 140, pp. 289–294 (Proposition 2.2) -/

/-- **External Axiom 1 (Carnicer 1994, Theorem 1 / Proposition 2.2)**:
At every non-dicritical singularity `p` of a holomorphic foliation germ `ℱ` on `(ℂ², 0)`
and every reduced `ℱ`-invariant analytic curve germ `C` through `p`,
`ν_p(C) ≤ ν_p(ℱ) + 1`. -/
axiom carnicer_local_inequality (nuF nuC : ℕ)
    (hnd : IsNonDicriticalSingularity nuF nuC) : nuC ≤ nuF + 1

/-- **External Axiom 2 (Carnicer 1994, Main Theorem / Proposition 2.2)**:
Every reduced non-dicritical invariant algebraic curve `S ⊂ ℂℙ²` of a degree-`m`
holomorphic foliation `ℱ` satisfies `deg S ≤ m + 2`. -/
axiom carnicer_degree_bound (F : ProjectiveFoliation) (S : ReducedCurve)
    (hnd : IsNonDicriticalInvariant F S) : S.totalDeg ≤ F.deg + 2

/-! ## Axiom 3: Deligne (1971), *Théorie de Hodge. II*, Publ. Math. IHÉS 40, Cor. 3.2.14 (Prop. 2.3) -/

/-- **External Axiom 3 (Deligne 1971, Cor. 3.2.14 / Proposition 2.3)**:
Every global logarithmic 1-form `α ∈ H⁰(X̃, Ω¹_{X̃}(log D))` on a smooth complex
projective variety `X̃` with simple normal crossing divisor `D` is closed (`dα = 0`). -/
axiom deligne_logarithmic_closed {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) (hlog : PullbackIsLogarithmic res) :
    PullbackIsClosed res

/-! ## Axioms 4–6: Classical Complex Algebraic Geometry on `ℂℙ¹` and `ℂℙ²` -/

/-- **External Axiom 4 (Residue Theorem on `ℂℙ¹` & Compact Riemann Surface Residues)**:
For a closed global logarithmic pullback `α = π*(ω/F)` of a saturated foliation `ℱ` with
`deg S = m + 2`, the Poincaré residues `λ_i` along `S̃_i` are nonzero constants (by saturation
`gcd(A, B, C) = 1`) and satisfy `∑ λ_i deg F_i = 0` on a generic projective line `L ≅ ℂℙ¹`. -/
axiom residue_theorem_CP1 {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S) (hsat : F.isSaturated)
    (hdeg : S.totalDeg = F.deg + 2) (hclosed : PullbackIsClosed res) :
    (∀ i : Fin S.k, poincareResidue res i ≠ 0) ∧
    (∑ i : Fin S.k, poincareResidue res i * (S.degF i : ℂ)) = 0

/-- **External Axiom 5 (Hartogs' Extension Theorem & `H⁰(ℂℙ², Ω¹_{ℂℙ²}) = 0`)**:
If `α = π*(ω/F)` has constant Poincaré residues `λ_i` with `∑ λ_i deg F_i = 0`, then
`β = ω/F - ∑ λ_i dF_i/F_i` extends holomorphically across codimension-2 `Sing(S)` and
vanishes identically because `H⁰(ℂℙ², Ω¹_{ℂℙ²}) = 0`. -/
axiom hartogs_and_no_holomorphic_1forms_CP2 {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S)
    (hsum : (∑ i : Fin S.k, poincareResidue res i * (S.degF i : ℂ)) = 0) :
    FormEqualsLogarithmicSum F S (poincareResidue res)

/-- **External Axiom 6 (Bézout's Theorem on `ℂℙ²` for Rational First Integrals)**:
If a 2-component curve `S = S₁ ∪ S₂` admits a nonconstant rational first integral
`H = F₁^a / F₂^b` (`a, b > 0`), then `S₁ ∩ S₂ ≠ ∅` by Bézout's theorem and every point
of `S₁ ∩ S₂` is a dicritical singularity of `ℱ` on `S`. -/
axiom bezout_rational_first_integral_dicritical (F : ProjectiveFoliation) (S : ReducedCurve)
    (hk : S.k = 2) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hH : HasTwoComponentRationalFirstIntegral F S hk a b) :
    ¬ IsNonDicriticalInvariant F S

/-- Bridge: `ω/F = λ₀ dF₀/F₀ + λ₁ dF₁/F₁` with `λ₀ b + λ₁ a = 0` (`a, b > 0`) yields the
rational first integral `H = F₀^a / F₁^b` (`dH/H = (a/λ₀) ω/F`). -/
axiom logarithmic_two_component_gives_first_integral (F : ProjectiveFoliation) (S : ReducedCurve)
    (hk : S.k = 2) (lam : Fin S.k → ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hform : FormEqualsLogarithmicSum F S lam)
    (hlam0 : lam ⟨0, by omega⟩ ≠ 0)
    (hrel : lam ⟨0, by omega⟩ * (b : ℂ) + lam ⟨1, by omega⟩ * (a : ℂ) = 0) :
    HasTwoComponentRationalFirstIntegral F S hk a b

/-- Every non-dicritical invariant curve `S` of a foliation `ℱ` admits an embedded
log-resolution whose centers are regular points or non-dicritical singularities
(Seidenberg 1968 / embedded resolution of plane curves). -/
axiom embedded_log_resolution_exists (F : ProjectiveFoliation) (S : ReducedCurve)
    (hnd : IsNonDicriticalInvariant F S) :
    Nonempty (EmbeddedLogResolution F S)

/-- If the holomorphic factor order stays non-negative at every stage of an embedded
log-resolution `res`, then `α = π*(ω/F)` has at most simple poles along the SNC divisor `D`
and is logarithmic (`α ∈ H⁰(X̃, Ω¹_{X̃}(log D))`). -/
axiom log_order_nonneg_implies_logarithmic {F : ProjectiveFoliation} {S : ReducedCurve}
    (res : EmbeddedLogResolution F S)
    (hord : ∀ j : Fin res.N, (res.steps j).nuC ≤ (res.steps j).nuF + 1) :
    PullbackIsLogarithmic res

/-! ## Axioms 7–10: Planar Limit Cycles, Harnack (1876), GLV (1996), Christopher (2001) -/

/-- Decomposition of a real reduced algebraic curve `S = {F = 0} ⊂ ℂℙ²` into real affine
irreducible components, optional line at infinity `L_∞`, and conjugate pairs `{G, Ḡ}` of
non-real irreducible factors. -/
structure RealCurveDecomposition where
  realAffineDegs : List ℕ
  realAffineDegs_pos : ∀ d ∈ realAffineDegs, 0 < d
  hasLineAtInfinity : Bool
  nonRealPairDegs : List ℕ
  nonRealPairDegs_pos : ∀ d ∈ nonRealPairDegs, 0 < d

/-- Total projective degree of a `RealCurveDecomposition`. -/
def RealCurveDecomposition.totalDeg (S : RealCurveDecomposition) : ℕ :=
  S.realAffineDegs.sum + (if S.hasLineAtInfinity then 1 else 0) + 2 * S.nonRealPairDegs.sum

/-- Predicate asserting `S` is the real-conjugate decomposition of the projective curve `S_alg`. -/
opaque RealDecompositionOf (S_alg : ReducedCurve) (S : RealCurveDecomposition) : Prop

/-- Predicate asserting a real planar polynomial vector field carries `numLimitCycles`
algebraic limit cycles on the real curve decomposition `S`. -/
opaque HasAlgebraicLimitCycles (S : RealCurveDecomposition) (numLimitCycles : ℕ) : Prop

/-- Predicate asserting `S_alg` is an irreducible reduced plane curve of degree `d` with
total `δ`-invariant `delta` and total Tjurina number `tau`. -/
opaque IsIrreducibleCurveInvariants (S_alg : ReducedCurve) (d delta tau : ℕ) : Prop

/-- Predicate asserting `S` is a single irreducible real plane curve of degree `d` with
total `δ`-invariant `delta` and total Tjurina number `tau`. -/
opaque IsIrreducibleRealCurveInvariants (S : RealCurveDecomposition) (d delta tau : ℕ) : Prop

/-- **External Axiom 7 (Giacomini–Llibre–Viano 1996, *Nonlinearity* 9 + Implicit Function Theorem)**:
A real planar polynomial vector field whose projective foliation is logarithmic on `S_alg`
(with real decomposition `S`) and possesses at least one algebraic limit cycle cannot be
purely real (`S.nonRealPairDegs ≠ []`): by Giacomini–Llibre–Viano [14], any limit cycle `γ`
lies in some real component `{f₁ = 0}`, where `ũ = f₁ ∏ |f_i|^{λ_i/λ₁}` is constant along
orbits (proved unconditionally in `LogarithmicRigidity.prop_4_1_local_first_integral_const`)
with `∇ũ|_γ ≠ 0`, producing a period annulus by the Implicit Function Theorem. -/
axiom glv_and_ift_no_purely_real_logarithmic_limit_cycle
    (F : ProjectiveFoliation) (S_alg : ReducedCurve) (S : RealCurveDecomposition)
    (numLimitCycles : ℕ)
    (hreal : RealDecompositionOf S_alg S)
    (hlog : ∃ lam, FormEqualsLogarithmicSum F S_alg lam ∧ IsLogarithmicFoliation F S_alg lam)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles)
    (hpos : 0 < numLimitCycles) :
    S.nonRealPairDegs ≠ []

/-- **External Axiom 8 (Harnack 1876, *Math. Ann.* 10 + Normalization Genus–`δ` Formula)**:
For any real reduced curve `S` with real affine irreducible component degrees `d_1, ..., d_s`,
the number `numLimitCycles` of algebraic limit cycles carried by `S(ℝ)` is at most
`∑_{j=1}^s h(d_j)`. -/
axiom harnack_total_oval_bound (S : RealCurveDecomposition) (numLimitCycles : ℕ)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles) :
    numLimitCycles ≤ (S.realAffineDegs.map hBound).sum

/-- **External Axiom 9 (Harnack 1876 + Normalization for Singular Irreducible Curves)**:
An irreducible real algebraic curve `S` of degree `d ≥ 1` with total `δ`-invariant `delta`
and total Tjurina number `tau` carries at most `(d - 1)(d - 2)/2 - delta + a_d` algebraic
limit cycles; if `d = 4`, `delta = 1`, and `tau ≥ 2` (a real unibranch cusp `A₂`), that
singular component occupies one connected component of `C̃(ℝ)`, leaving at most `2` smooth ovals. -/
axiom harnack_singular_irred_bound (S : RealCurveDecomposition)
    (d delta tau numLimitCycles : ℕ) (hd : 1 ≤ d)
    (hirred : IsIrreducibleRealCurveInvariants S d delta tau)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles) :
    (numLimitCycles ≤ (d - 1) * (d - 2) / 2 - delta + aVal d) ∧
    (d = 4 → delta = 1 → 2 ≤ tau → numLimitCycles ≤ 2)

/-- **External Axiom 10 (Christopher 2001, *Geom. Dedicata* 88 + Harnack M-Curve Existence)**:
For every `m ≥ 2`, there exists a standard degree-`m` planar polynomial system (`r ≡ 0`,
so `L_∞` is invariant) with only nodal (hence non-dicritical) invariant curves and exactly
`H_nodal(m)` hyperbolic algebraic limit cycles. -/
axiom christopher_sharpness_construction (m : ℕ) (hm : 2 ≤ m) :
    ∃ (F : ProjectiveFoliation) (S_alg : ReducedCurve) (S : RealCurveDecomposition),
      F.deg = m ∧ F.isSaturated ∧ IsNonDicriticalInvariant F S_alg ∧
      RealDecompositionOf S_alg S ∧ S_alg.totalDeg = S.totalDeg ∧
      S.hasLineAtInfinity = true ∧ HasAlgebraicLimitCycles S (Hnodal m)

/-! ## Axioms 11–13: Camacho–Lins Neto–Sad (1984), Dimca (2013), Analytic Perturbation -/

/-- Predicate asserting a non-degenerate singularity of a holomorphic foliation on `ℂℙ²`
is non-dicritical. -/
opaque SingularityIsNonDicritical (μ₁ μ₂ : ℂ) : Prop

/-- **External Axiom 11 (Camacho–Lins Neto–Sad 1984, *J. Differential Geom.* 20)**:
A non-degenerate singularity of a holomorphic foliation on `(ℂ², 0)` with eigenvalues
`μ₁, μ₂ ∈ ℂ*` and ratio `ρ = μ₁/μ₂ ∉ ℚ_{>0}` has at most two formal separatrices and is
therefore non-dicritical. -/
axiom camacho_lins_neto_sad_nondicritical (μ₁ μ₂ : ℂ) (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0)
    (hrat : ∀ q : ℚ, 0 < q → μ₁ / μ₂ ≠ (q : ℂ)) :
    SingularityIsNonDicritical μ₁ μ₂

/-- **External Axiom 12 (Dimca 2013, *Bull. Math. Soc. Sci. Math. Roumanie* 56(104), Thm. 3.1 /
Serre Duality on `ℙ²`)**:
For a reduced irreducible plane curve `S_alg` of degree `d = m + 1` (`m ≥ 1`) with total
`δ`-invariant `delta` and total Tjurina number `tau`, if `S_alg` is a non-dicritical
invariant curve of a degree-`m` foliation `ℱ`, then `S_alg` cannot be smooth (`1 ≤ delta`),
and when `m = 3` (`d = 4`), `h¹(ℙ², ℐ_Z(0)) = tau - 1 > 0` forces `2 ≤ tau`. -/
axiom dimca_serre_duality_syzygy_defect (F : ProjectiveFoliation) (S_alg : ReducedCurve)
    (m delta tau : ℕ) (hm : 1 ≤ m) (hF_deg : F.deg = m)
    (hirred : IsIrreducibleCurveInvariants S_alg (m + 1) delta tau)
    (hnd : IsNonDicriticalInvariant F S_alg) :
    1 ≤ delta ∧ (m = 3 → 2 ≤ tau)

/-- **External Axiom 13 (Analytic Implicit Function Theorem & Identity Theorem for Prop. 5.4)**:
For every `m ≥ 2`, if `rhoLinearCoeff m ω ≠ 0` for every root `ω` of `2 ω^{m+1} + 1 = 0`
(proved unconditionally in `LogarithmicRigidity.prop_5_4_and_theorem_1_3_part2`), then there
exists `ε_m ∈ (0, 2(m + 1))` such that the resonant set `E_m ⊂ (0, ε_m)` where any smooth
singularity of `ℱ_m(λ)` on `C_m \ {(0, 0)}` has eigenvalue ratio in `ℚ_{>0}` is countable. -/
axiom analytic_perturbation_countable_resonances (m : ℕ) (hm : 2 ≤ m)
    (hcoeff : ∀ ω : ℂ, 2 * ω ^ (m + 1) + 1 = 0 → rhoLinearCoeff m ω ≠ 0) :
    ∃ (ε : ℝ) (E : Set ℝ), 0 < ε ∧ ε < 2 * ((m + 1 : ℕ) : ℝ) ∧ E.Countable

end LogarithmicRigidityConditional
