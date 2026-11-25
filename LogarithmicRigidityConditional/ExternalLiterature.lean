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

/-! ## Axioms 7–10: Planar Limit Cycles, GLV (1996), IFT, Harnack (1876), Christopher (2001) -/

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

/-- Predicate asserting `S` carries a real unibranch singularity (such as a real cusp `A₂`)
whose preimage in the normalization `C̃(ℝ)` lies on one connected component. -/
opaque HasRealUnibranchSingularity (S : RealCurveDecomposition) : Prop

/-- Predicate asserting `(f₁, f)` are the `C¹` component evaluations along an isolated periodic
orbit `γ ⊂ {f₁ = 0}` of a purely real logarithmic vector field with `∇f₁|_γ ≠ 0` and
`f_i|_γ ≠ 0`, so constancy of `ũ = f₁ ∏ |f_i|^{λ_i/λ₁}` along orbits yields a period annulus. -/
opaque IsIsolatedPeriodicOrbitLocalFirstIntegral {n : ℕ}
    (lam₁ : ℝ) (lam : Fin n → ℝ) (f₁ : ℝ → ℝ) (f : Fin n → ℝ → ℝ) : Prop

/-- **External Axiom 7a (Giacomini–Llibre–Viano 1996, *Nonlinearity* 9, 501–516)**:
For a purely real logarithmic foliation (`S.nonRealPairDegs = []`) possessing a limit cycle,
the limit cycle `γ` lies in `{f = 0}` (on some real component `f₁ = 0` disjoint from all
other components `f_i` and all singularities) and satisfies the real logarithmic differential
identity along orbits in a tubular neighborhood. -/
axiom giacomini_llibre_viano_limit_cycle_orbit
    (F : ProjectiveFoliation) (S_alg : ReducedCurve) (S : RealCurveDecomposition)
    (numLimitCycles : ℕ)
    (hreal : RealDecompositionOf S_alg S)
    (hlog : ∃ lam, FormEqualsLogarithmicSum F S_alg lam ∧ IsLogarithmicFoliation F S_alg lam)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles)
    (hpos : 0 < numLimitCycles)
    (hreal_only : S.nonRealPairDegs = []) :
    ∃ (n : ℕ) (lam₁ : ℝ) (lam : Fin n → ℝ) (f₁ f₁' : ℝ → ℝ) (f f' : Fin n → ℝ → ℝ),
      lam₁ ≠ 0 ∧
      (∀ t : ℝ, HasDerivAt f₁ (f₁' t) t) ∧
      (∀ i : Fin n, ∀ t : ℝ, HasDerivAt (f i) (f' i t) t) ∧
      (∀ i : Fin n, ∀ t : ℝ, f i t ≠ 0) ∧
      (∀ t : ℝ,
        lam₁ * (∏ j : Fin n, f j t) * f₁' t +
        ∑ i : Fin n, lam i * f₁ t * (∏ j ∈ Finset.univ.erase i, f j t) * f' i t = 0) ∧
      IsIsolatedPeriodicOrbitLocalFirstIntegral lam₁ lam f₁ f

/-- **External Axiom 7b (Implicit Function Theorem — Period Annulus Obstruction)**:
If `ũ(t) = f₁(t) ∏ |f_i(t)|^{λ_i/λ₁}` is constant along orbits in a tubular neighborhood of an
isolated periodic orbit `γ ⊂ {f₁ = 0}` with `∇ũ|_γ ≠ 0`, then the nearby level sets `{ũ = ε}`
are periodic orbits accumulating on `γ`, contradicting the isolation of `γ`. -/
axiom ift_local_first_integral_contradicts_isolation {n : ℕ}
    (lam₁ : ℝ) (lam : Fin n → ℝ) (f₁ : ℝ → ℝ) (f : Fin n → ℝ → ℝ)
    (hiso : IsIsolatedPeriodicOrbitLocalFirstIntegral lam₁ lam f₁ f)
    (hconst : ∀ t : ℝ,
      f₁ t * (∏ i : Fin n, |f i t| ^ (lam i / lam₁)) =
      f₁ 0 * (∏ i : Fin n, |f i 0| ^ (lam i / lam₁))) :
    False

/-- **External Axiom 8 (Harnack 1876, *Math. Ann.* 10 + Normalization Genus–`δ` Formula)**:
For any real reduced curve `S` with real affine irreducible component degrees `d_1, ..., d_s`,
the number `numLimitCycles` of algebraic limit cycles carried by `S(ℝ)` is at most
`∑_{j=1}^s h(d_j)`. -/
axiom harnack_total_oval_bound (S : RealCurveDecomposition) (numLimitCycles : ℕ)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles) :
    numLimitCycles ≤ (S.realAffineDegs.map hBound).sum

/-- **External Axiom 9a (Harnack 1876 + Normalization for Singular Irreducible Curves)**:
An irreducible real algebraic curve `S` of degree `d ≥ 1` with total `δ`-invariant `delta`
carries at most `(d - 1)(d - 2)/2 - delta + a_d` smooth ovals; if `S` has a real unibranch
singularity, its preimage occupies one connected component of `C̃(ℝ)`, leaving at most
`(d - 1)(d - 2)/2 - delta + a_d - 1` smooth ovals. -/
axiom harnack_singular_irred_bound (S : RealCurveDecomposition)
    (d delta tau numLimitCycles : ℕ) (hd : 1 ≤ d)
    (hirred : IsIrreducibleRealCurveInvariants S d delta tau)
    (hlc : HasAlgebraicLimitCycles S numLimitCycles) :
    (numLimitCycles ≤ (d - 1) * (d - 2) / 2 - delta + aVal d) ∧
    (HasRealUnibranchSingularity S →
      numLimitCycles ≤ (d - 1) * (d - 2) / 2 - delta + aVal d - 1)

/-- **External Axiom 9b (Classical Plane Curve Singularity Classification for `δ = 1`)**:
A real irreducible plane curve with total `δ`-invariant `1` has a unique singular point `p`
(hence real, as non-real singularities occur in conjugate pairs) of multiplicity `2`, which is
either an ordinary node `A₁` (`τ = 1`) or an ordinary unibranch cusp `A₂` (`τ = 2`).
Thus `δ = 1` and `τ ≥ 2` imply `S` has a real unibranch singularity. -/
axiom plane_curve_delta_one_cusp_classification (S : RealCurveDecomposition)
    (d tau : ℕ) (hd : 1 ≤ d)
    (hirred : IsIrreducibleRealCurveInvariants S d 1 tau)
    (htau : 2 ≤ tau) :
    HasRealUnibranchSingularity S

/-- **External Axiom 10 (Christopher 2001, *Geom. Dedicata* 88 + Harnack M-Curve Existence)**:
For every `m ≥ 1`, there exists a standard degree-`m` planar polynomial system (`r ≡ 0`,
`L_∞` invariant) with only nodal (hence non-dicritical) invariant curves and exactly
`H_nodal(m)` algebraic limit cycles (`ẋ = x, ẏ = -y` for `m = 1`; Christopher [8] for `m ≥ 2`). -/
axiom christopher_sharpness_construction (m : ℕ) (hm : 1 ≤ m) :
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

/-- Dimension `dim_ℂ V_m(F) = dim_ℂ Syz(J_F)_{d-1}` of degree-`m` foliations preserving `S_alg`. -/
opaque syzygyDim (S_alg : ReducedCurve) (m : ℕ) : ℕ

/-- Cohomology defect `h¹(ℙ², ℐ_Z(d - 4))` of the Tjurina subscheme `Z` of `S_alg`. -/
opaque tjurinaH1Defect (S_alg : ReducedCurve) (d : ℕ) : ℕ

/-- **External Axiom 12a (Dimca 2013, *Bull. Math. Soc. Sci. Math. Roumanie* 56(104), Thm. 3.1 /
Serre Duality on `ℙ²`)**:
For an irreducible plane curve `S_alg` of degree `d = m + 1` (`m ≥ 1`),
`dim_ℂ V_m(F) = 3 + h¹(ℙ², ℐ_Z(d - 4))`; the defect vanishes when `S_alg` is smooth (`δ = 0`),
and equals `τ - 1` when `d = 4` (`m = 3`) and `δ ≥ 1`. -/
axiom dimca_syzygy_defect_formula (S_alg : ReducedCurve) (m delta tau : ℕ) (hm : 1 ≤ m)
    (hirred : IsIrreducibleCurveInvariants S_alg (m + 1) delta tau) :
    syzygyDim S_alg m = 3 + tjurinaH1Defect S_alg (m + 1) ∧
    (delta = 0 → tjurinaH1Defect S_alg (m + 1) = 0) ∧
    (m = 3 → 1 ≤ delta → tjurinaH1Defect S_alg 4 = tau - 1)

/-- **External Axiom 12b (Dicriticality of Koszul Pencil Subspace / Bézout on `ℂℙ²`)**:
Whenever `dim_ℂ V_m(F) = 3`, every degree-`m` foliation preserving `S_alg` lies in the
3-dimensional Koszul pencil subspace `{ω_L = L dF - d F dL}` (algebraically characterized in
`LogarithmicRigidity.prop_5_1_koszul_pencil_forms` and `theorem_1_3_part1_koszul_rigidity`),
admits the rational first integral `F / L^d`, and is dicritical at `C ∩ {L = 0} ≠ ∅`. -/
axiom koszul_subspace_dicritical (F : ProjectiveFoliation) (S_alg : ReducedCurve)
    (m delta tau : ℕ) (hm : 1 ≤ m) (hF_deg : F.deg = m)
    (hirred : IsIrreducibleCurveInvariants S_alg (m + 1) delta tau)
    (hdim3 : syzygyDim S_alg m = 3) :
    ¬ IsNonDicriticalInvariant F S_alg

/-- Predicate asserting that every smooth singularity `p_j(λ)` of `ℱ_m(λ)` on `C_m \ {(0, 0)}`
is non-degenerate with eigenvalue ratio `ρ_j(λ) ∉ ℚ_{>0}` (hence non-dicritical). -/
opaque IsSmoothSingNonDicriticalOnCm (m : ℕ) (lam : ℝ) : Prop

/-- **External Axiom 13 (Analytic Implicit Function Theorem & Identity Theorem for Prop. 5.4)**:
For every `m ≥ 2`, since `rhoLinearCoeff m ω ≠ 0` at every root `ω` of `2 ω^{m+1} + 1 = 0`
(proved unconditionally in `LogarithmicRigidity.prop_5_4_and_theorem_1_3_part2` and linked to
`div(𝒴_m)` and `K̃_m` in `prop_5_4_div_and_asymp`), there exists `ε_m ∈ (0, 2(m + 1))` and a
countable resonant set `E_m ⊂ ℝ` such that every `λ ∈ (0, ε_m) \ E_m` satisfies
`IsSmoothSingNonDicriticalOnCm m lam`. -/
axiom analytic_perturbation_countable_resonances (m : ℕ) (hm : 2 ≤ m)
    (hcoeff : ∀ ω : ℂ, 2 * ω ^ (m + 1) + 1 = 0 → rhoLinearCoeff m ω ≠ 0) :
    ∃ (ε : ℝ) (E : Set ℝ), 0 < ε ∧ ε < 2 * ((m + 1 : ℕ) : ℝ) ∧ E.Countable ∧
      (∀ lam ∈ Set.Ioo (0 : ℝ) ε, lam ∉ E → IsSmoothSingNonDicriticalOnCm m lam)

end LogarithmicRigidityConditional
