/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import Mathlib

/-!
# Public Definitions for Logarithmic Rigidity and Algebraic Limit Cycles

This module contains ONLY genuine mathematical definitions built directly on Lean 4 core
and Mathlib `v4.35.0` (zero custom axioms, zero hypothesis-bundle shortcuts).
-/

namespace LogarithmicRigidity

/-! ## Section 1–2: Combinatorial Oval Bounds and Non-Dicriticality Criterion -/

/-- Parity indicator `a_m`: `1` if `m` is even, `0` if `m` is odd (Equation (1.2)). -/
def aVal (m : ℕ) : ℕ :=
  if Even m then 1 else 0

/-- Nodal algebraic limit cycle bound `H_nodal(m) = (m - 1)(m - 2) / 2 + a_m` (Equation (1.2)). -/
def Hnodal (m : ℕ) : ℕ :=
  (m - 1) * (m - 2) / 2 + aVal m

/-- Extended Harnack oval bound function `h : ℕ → ℕ` (Equation (2.3)). -/
def hBound : ℕ → ℕ
  | 0 => 0
  | d => (d - 1) * (d - 2) / 2 + aVal d

/-- Sharpened upper bound for `r ≢ 0` in Theorem 1.4(1). -/
def rNonZeroBound : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | m => m * (m - 1) / 2 - 1 + aVal (m + 1)

/-- Projectively invariant ratio `τ = (tr J)² / det J` at a non-degenerate singularity (Eq. (2.2)). -/
noncomputable def tauRatio (tr det : ℂ) : ℂ :=
  tr ^ 2 / det

/-- Predicate asserting that `τ` lies in the real ray `[4, ∞)`. -/
def InRealRayFour (τ : ℂ) : Prop :=
  τ.im = 0 ∧ (4 : ℝ) ≤ τ.re

/-- Predicate asserting that `τ ∉ [4, ∞)` (algebraic non-dicriticality criterion, Lemma 2.1). -/
def IsNonDicriticalTau (τ : ℂ) : Prop :=
  ¬ InRealRayFour τ

/-- Induced homogeneous 1-form `(A, B, C)` of degree `m + 1` from an affine system
`P = p + x * r`, `Q = q + y * r` (Equation (2.1)). -/
structure InducedOneForm (R : Type*) [CommRing R] where
  X : R
  Y : R
  Z : R
  Ph : R
  Qh : R
  Rh : R

/-- Component `A = Z * Qh + Y * Rh` of the induced homogeneous 1-form (2.1). -/
def InducedOneForm.A {R : Type*} [CommRing R] (ω : InducedOneForm R) : R :=
  ω.Z * ω.Qh + ω.Y * ω.Rh

/-- Component `B = -(Z * Ph + X * Rh)` of the induced homogeneous 1-form (2.1). -/
def InducedOneForm.B {R : Type*} [CommRing R] (ω : InducedOneForm R) : R :=
  -(ω.Z * ω.Ph + ω.X * ω.Rh)

/-- Component `C = Y * Ph - X * Qh` of the induced homogeneous 1-form (2.1). -/
def InducedOneForm.C {R : Type*} [CommRing R] (ω : InducedOneForm R) : R :=
  ω.Y * ω.Ph - ω.X * ω.Qh

/-! ## Section 5: Jacobian Syzygies and Degree-`(m + 1)` Irreducible Curves -/

/-- Section 5 curve `f_m(x, y) = x^m - y^m + x^{m+1} + 2 y^{m+1}` (Equation (5.2)). -/
def fmPoly (m : ℕ) (x y : ℂ) : ℂ :=
  x ^ m - y ^ m + x ^ (m + 1) + 2 * y ^ (m + 1)

/-- Partial derivative `∂f_m/∂x = (m + 1) x^{m-1} (x + m/(m+1))`. -/
def fmDx (m : ℕ) (x _y : ℂ) : ℂ :=
  (m : ℂ) * x ^ (m - 1) + ((m + 1 : ℕ) : ℂ) * x ^ m

/-- Partial derivative `∂f_m/∂y = 2(m + 1) y^{m-1} (y - m/(2(m+1)))`. -/
def fmDy (m : ℕ) (_x y : ℂ) : ℂ :=
  -((m : ℂ) * y ^ (m - 1)) + 2 * ((m + 1 : ℕ) : ℂ) * y ^ m

/-- Rational parametrization `x(t) = (t^m - 1) / (1 + 2 t^{m+1})` (Equation (5.5)). -/
noncomputable def xParam (m : ℕ) (t : ℂ) : ℂ :=
  (t ^ m - 1) / (1 + 2 * t ^ (m + 1))

/-- Rational parametrization `y(t) = t * x(t)` (Equation (5.5)). -/
noncomputable def yParam (m : ℕ) (t : ℂ) : ℂ :=
  t * xParam m t

/-- Vector field component `P_m(x, y; λ)` (Equation (5.3)). -/
noncomputable def PmVec (m : ℕ) (lam x y : ℂ) : ℂ :=
  -fmDy m x y + lam * x ^ (m - 1) * (x + 1) * (y - (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ)))

/-- Vector field component `Q_m(x, y; λ)` (Equation (5.4)). -/
noncomputable def QmVec (m : ℕ) (lam x y : ℂ) : ℂ :=
  fmDx m x y + lam * x ^ (m - 2) * y * (y - (1 : ℂ) / 2) * (x + (m : ℂ) / ((m + 1 : ℕ) : ℂ))

/-- Cofactor `K_m(x, y; λ)` (Equation (5.6)). -/
noncomputable def KmCof (m : ℕ) (lam x y : ℂ) : ℂ :=
  lam * ((m + 1 : ℕ) : ℂ) * x ^ (m - 2) *
    (x + (m : ℂ) / ((m + 1 : ℕ) : ℂ)) * (y - (m : ℂ) / (2 * ((m + 1 : ℕ) : ℂ)))

/-- Auxiliary polynomial `g_m(t; λ) = 2(m + 1)(2 t^{m+1} + 1) - λ t(2t + 1)` (Proposition 5.4). -/
def gmPoly (m : ℕ) (lam t : ℂ) : ℂ :=
  2 * ((m + 1 : ℕ) : ℂ) * (2 * t ^ (m + 1) + 1) - lam * t * (2 * t + 1)

/-- Linear `λ`-coefficient of `ρ_j(λ)` at a root `ω` of `2 ω^{m+1} + 1 = 0` (Proposition 5.4). -/
noncomputable def rhoLinearCoeff (m : ℕ) (ω : ℂ) : ℂ :=
  ((((m : ℂ) - 1) / 2 - ω) * (2 * ω + 1)) / (2 * (((m + 1 : ℕ) : ℂ) ^ 3) * (ω ^ m - 1))

/-! ## Section 6 & Appendix A: Explicit 2-Nodal Quartic and Degree-3 Counterexample -/

/-- Explicit 2-nodal quartic `f(x, y)` (Equation (6.1)). -/
def quarticF {R : Type*} [CommRing R] (x y : R) : R :=
  2 * x ^ 4 + x ^ 3 - 2 * x ^ 2 * y ^ 2 + x ^ 2 * y - 8 * x ^ 2 + 2 * y ^ 4 + 4 * y ^ 2 + 2

/-- Partial derivative `∂f/∂x` of the quartic (6.1). -/
def quarticFx {R : Type*} [CommRing R] (x y : R) : R :=
  8 * x ^ 3 + 3 * x ^ 2 - 4 * x * y ^ 2 + 2 * x * y - 16 * x

/-- Partial derivative `∂f/∂y` of the quartic (6.1). -/
def quarticFy {R : Type*} [CommRing R] (x y : R) : R :=
  -4 * x ^ 2 * y + x ^ 2 + 8 * y ^ 3 + 8 * y

/-- Leading homogeneous quartic part `F_4(X, Y) = 2(X⁴ - X²Y² + Y⁴)`. -/
def quarticF4 {R : Type*} [CommRing R] (X Y : R) : R :=
  2 * (X ^ 4 - X ^ 2 * Y ^ 2 + Y ^ 4)

/-- Vector field component `P(x, y)` (Equation (6.2)). -/
def vecP {R : Type*} [CommRing R] (x y : R) : R :=
  8 * x ^ 3 + 172 * x ^ 2 * y - 39 * x ^ 2 + 48 * x * y ^ 3 + 12 * x * y ^ 2 -
    48 * x * y - 4 * x - 312 * y ^ 3 - 312 * y

/-- Vector field component `Q(x, y)` (Equation (6.2)). -/
def vecQ {R : Type*} [CommRing R] (x y : R) : R :=
  320 * x ^ 3 + 16 * x ^ 2 * y + 21 * x ^ 2 - 144 * x * y ^ 2 + 78 * x * y -
    612 * x + 48 * y ^ 4 + 8 * y ^ 3 + 48 * y ^ 2 + 8 * y

/-- Cofactor `K(x, y)` for the counterexample system (Proposition 6.2). -/
def cofactorK {R : Type*} [CommRing R] (x y : R) : R :=
  32 * x ^ 2 + 48 * x * y + 192 * y ^ 3 + 32 * y ^ 2

/-- Jacobian trace `tr J(x, y) = P_x + Q_y` of the counterexample system (6.2). -/
def jacTr {R : Type*} [CommRing R] (x y : R) : R :=
  (24 * x ^ 2 + 344 * x * y - 78 * x + 48 * y ^ 3 + 12 * y ^ 2 - 48 * y - 4) +
  (16 * x ^ 2 - 288 * x * y + 78 * x + 192 * y ^ 3 + 24 * y ^ 2 + 96 * y + 8)

/-- Jacobian determinant `det J(x, y) = P_x Q_y - P_y Q_x` of the counterexample system (6.2). -/
def jacDet {R : Type*} [CommRing R] (x y : R) : R :=
  (24 * x ^ 2 + 344 * x * y - 78 * x + 48 * y ^ 3 + 12 * y ^ 2 - 48 * y - 4) *
    (16 * x ^ 2 - 288 * x * y + 78 * x + 192 * y ^ 3 + 24 * y ^ 2 + 96 * y + 8) -
  (172 * x ^ 2 + 144 * x * y ^ 2 + 24 * x * y - 48 * x - 936 * y ^ 2 - 312) *
    (960 * x ^ 2 + 32 * x * y + 42 * x - 144 * y ^ 2 + 78 * y - 612)

/-- Irreducible degree-4 resultant factor `q_4(x)` (Proposition 6.2). -/
def q4Poly {R : Type*} [CommRing R] (x : R) : R :=
  2304 * x ^ 4 - 44160 * x ^ 3 + 352880 * x ^ 2 - 1354536 * x + 2169793

/-- Irreducible degree-6 resultant factor `q_6(x)` (Proposition 6.2). -/
def q6Poly {R : Type*} [CommRing R] (x : R) : R :=
  6144000 * x ^ 6 + 2645104 * x ^ 5 - 36117968 * x ^ 4 - 10114508 * x ^ 3 +
    70562515 * x ^ 2 + 9639428 * x - 45929728

/-- Minimal polynomial `M_4(τ)` of `τ` on the `q_4 = 0` stratum (Appendix A). -/
def M4Poly {R : Type*} [CommRing R] (τ : R) : R :=
  90300372977677627797217040238637109248 * τ ^ 4 -
  2279558135214916933942611069746197644288 * τ ^ 3 +
  21580251865599942120239917323725565102528 * τ ^ 2 -
  90801612796538526687818920091684644325136 * τ +
  143276813705244499010518737554045186664681

/-- Minimal polynomial `M_6(τ)` of `τ` on the `q_6 = 0` stratum (Appendix A). -/
def M6Poly {R : Type*} [CommRing R] (τ : R) : R :=
  9085066411799807613360657507731924859835476058112 * τ ^ 6 -
  148638225088493798824420464853313190892178489600 * τ ^ 5 +
  1011925311981483113020798910403905630277557568 * τ ^ 4 -
  3673940314571771932230387313318209571442400 * τ ^ 3 +
  7506981684801179908056588918973370174874 * τ ^ 2 -
  8177684530001167096699229867010973851 * τ +
  3696784356897634041034466249235600

/-- Scaled auxiliary polynomial `32000 * g_1(x, y)` (Proposition 6.3). -/
def g1Scaled {R : Type*} [CommRing R] (x y : R) : R :=
  -2713 * x ^ 3 + 678 * x ^ 2 * y - 15081 * x ^ 2 - 18 * x * y ^ 2 +
    2399 * x * y - 6176 * x + 111 * y ^ 3 + 2186 * y ^ 2 + 1537 * y

/-- Scaled shifted cofactor `32000 * H_1(x, y) = 32000 * (K + P g_{1,x} + Q g_{1,y})`. -/
def H1Scaled {R : Type*} [CommRing R] (x y : R) : R :=
  32000 * cofactorK x y +
    vecP x y * (-8139 * x ^ 2 + 1356 * x * y - 30162 * x - 18 * y ^ 2 + 2399 * y - 6176) +
    vecQ x y * (678 * x ^ 2 - 36 * x * y + 2399 * x + 333 * y ^ 2 + 4372 * y + 1537)

/-- Scaled auxiliary polynomial `3200 * g_2(x, y)` (Proposition 6.3). -/
def g2Scaled {R : Type*} [CommRing R] (x y : R) : R :=
  762 * x ^ 2 + 77 * x * y + 879 * x - 510 * y ^ 2 - 142 * y

/-- Scaled shifted cofactor `3200 * H_2(x, y) = 3200 * (K + P g_{2,x} + Q g_{2,y})`. -/
def H2Scaled {R : Type*} [CommRing R] (x y : R) : R :=
  3200 * cofactorK x y +
    vecP x y * (1524 * x + 77 * y + 879) +
    vecQ x y * (77 * x - 1020 * y - 142)

end LogarithmicRigidity
