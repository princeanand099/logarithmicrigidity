/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.CounterexampleCert
import LogarithmicRigidity.Section6ElimCert

/-!
# Section 6 (`q₄` Stratum Non-Dicriticality Certificate)

Proves unconditionally on top of Mathlib `v4.35.0` (zero custom axioms) that every
complex affine singularity `(x, y)` of the degree-3 counterexample `(P, Q)` (6.2) lying
on the `q₄(x) = 0` stratum of `sing_PQ_elim` satisfies:
1. `jacDet x y ≠ 0` (non-degenerate singularity), and
2. `IsNonDicriticalTau (tauRatio (jacTr x y) (jacDet x y))` (`τ ∉ [4, ∞)`).

Method:
- 3-step linear `y`-elimination `linA x * y + linB x = 0` with Bézout coprimality
  `gcd(q₄, linA) = 1` uniquely identifies `y = y₄(x) = -6 x² + (115/2) x - 1473/8`.
- Exact polynomial reductions mod `q₄(x)` yield `jacTr`, `jacDet`, Bézout inverse
  `detR * invD ≡ 1 (mod q₄)`, `tauR ≡ trR² / detR (mod q₄)`, and 4-step Horner
  reduction proves `M₄(tauR) = 0`.
- Strict real positivity `M₄(t) > 0` for all `t ∈ ℝ` (`prop_6_2_counterexample_nondicritical`)
  then implies `τ ∉ ℝ`, hence `τ ∉ [4, ∞)`.
-/

namespace LogarithmicRigidity

set_option maxHeartbeats 1000000

private def q4LinA (x : ℂ) : ℂ :=
  1821312 * x ^ 5 - 23036448 * x ^ 4 + 104728664 * x ^ 3 - 116008732 * x ^ 2 -
    248369187 * x + 328945695

private def q4LinB (x : ℂ) : ℂ :=
  46080 * x ^ 6 + 316128 * x ^ 5 - 9313592 * x ^ 4 + 54454966 * x ^ 3 -
    116314829 * x ^ 2 - 89704058 * x + 221114400

private noncomputable def y4Expr (x : ℂ) : ℂ :=
  (-(6) : ℂ) * x ^ 2 + ((115 : ℂ) / (2 : ℂ)) * x + (-(1473 : ℂ) / (8 : ℂ))

private lemma q4_sing_PQ_linear_y (x y : ℂ) (hP : vecP x y = 0) (hQ : vecQ x y = 0)
    (hx : x ≠ 0) (hx13 : 2 * x - 13 ≠ 0) :
    q4LinA x * y + q4LinB x = 0 := by
  let R1 : ℂ := (2 * x - 13) * vecQ x y - 2 * y * vecP x y
  let R2 : ℂ := (x + 13) * vecP x y + 3 * (2 * x - 13) * R1
  let R3a : ℂ := (-x * (4 * x - 13) * (79 * x - 515)) * vecP x y - (2 * (2 * x - 13)) * y * R2
  let R3 : ℂ := (-3 * (4 * x - 13) * (79 * x - 515)) * R3a -
    (-96 * x ^ 4 - 28 * x ^ 3 + 12103 * x ^ 2 - 88114 * x + 240825) * R2
  have hR1 : R1 = 0 := by simp [R1, hP, hQ]
  have hR2 : R2 = 0 := by simp [R2, hP, hR1]
  have hR3a : R3a = 0 := by simp [R3a, hP, hR2]
  have hR3 : R3 = 0 := by simp [R3, hR3a, hR2]
  have hid : R3 = 2 * x * (2 * x - 13) ^ 2 * (q4LinA x * y + q4LinB x) := by
    simp only [R3, R3a, R2, R1, vecP, vecQ, q4LinA, q4LinB]
    ring
  rw [hid] at hR3
  have hfac : 2 * x * (2 * x - 13) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hx) (pow_ne_zero 2 hx13)
  exact (mul_eq_zero.mp hR3).resolve_left hfac

private lemma q4_y_eq (x y : ℂ) (hP : vecP x y = 0) (hQ : vecQ x y = 0)
    (hq : q4Poly x = 0) : y = y4Expr x := by
  have hx : x ≠ 0 := by
    intro h0; subst h0; unfold q4Poly at hq; norm_num at hq
  have hx13 : 2 * x - 13 ≠ 0 := by
    intro h0
    have hxval : x = 13 / 2 := by linear_combination h0 / 2
    rw [hxval] at hq
    unfold q4Poly at hq
    norm_num at hq
  have hlin := q4_sing_PQ_linear_y x y hP hQ hx hx13
  have hlin4 : q4LinA x * y4Expr x + q4LinB x = 0 := by
    have hid : q4LinA x * y4Expr x + q4LinB x =
        ((-(4743) : ℂ) * x ^ 3 +
         (14557 : ℂ) * x ^ 2 +
         ((99119 : ℂ) / 8) * x +
         (-(222495 : ℂ) / 8)) * q4Poly x := by
      simp only [q4LinA, q4LinB, y4Expr, q4Poly]; ring
    rw [hid, hq, mul_zero]
  have hA_ne : q4LinA x ≠ 0 := by
    have hbez :
        ((-(5989555301084197710245747875008 : ℂ) / 3514919099912536938903039124405898183) * x ^ 4 +
         ((53838843680652805342592605934048 : ℂ) / 3514919099912536938903039124405898183) * x ^ 3 +
         (-(278081794945192717178905650014200 : ℂ) / 10544757299737610816709117373217694549) * x ^ 2 +
         (-(126407835995871263982153882107916 : ℂ) / 3514919099912536938903039124405898183) * x +
         ((16101673148523665651391784493647 : ℂ) / 270378392300964379915618394185069091)) * q4Poly x +
        (((7576920051972419620804235136 : ℂ) / 3514919099912536938903039124405898183) * x ^ 3 +
         (-(117496690934163005769988398112 : ℂ) / 3514919099912536938903039124405898183) * x ^ 2 +
         ((1983939003774193550092828711960 : ℂ) / 10544757299737610816709117373217694549) * x +
         (-(4110130860513289835599684374796 : ℂ) / 10544757299737610816709117373217694549)) * q4LinA x = 1 := by
      simp only [q4Poly, q4LinA]; ring
    intro h0
    rw [hq, h0, mul_zero, mul_zero, add_zero] at hbez
    exact zero_ne_one hbez
  have hdiff : q4LinA x * (y - y4Expr x) = 0 := by linear_combination hlin - hlin4
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hA_ne)

private lemma q4_det_and_M4 (x : ℂ) (hq : q4Poly x = 0) :
    jacDet x (y4Expr x) ≠ 0 ∧
    M4Poly (tauRatio (jacTr x (y4Expr x)) (jacDet x (y4Expr x))) = 0 := by
  set y1 : ℂ := y4Expr x
  set y2 : ℂ := (2 : ℂ) * x ^ 2 + (-(39 : ℂ) / (4 : ℂ)) * x + (-(1) : ℂ)
  set y3 : ℂ := (-(113 : ℂ) / (2 : ℂ)) * x ^ 3 + ((21961 : ℂ) / (24 : ℂ)) * x ^ 2 +
    (-(170149 : ℂ) / (32 : ℂ)) * x + ((2205145 : ℂ) / (192 : ℂ))
  have hy2 : y1 ^ 2 = y2 := by
    have hid : y1 ^ 2 - y2 = (((1 : ℂ) / (64 : ℂ))) * q4Poly x := by
      simp only [y1, y2, y4Expr, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have hy3 : y1 ^ 3 = y3 := by
    have hpow : y1 ^ 3 = y1 ^ 2 * y1 := by ring
    rw [hpow, hy2]
    have hid : y2 * y1 - y3 = ((-(1 : ℂ) / (192 : ℂ))) * q4Poly x := by
      simp only [y1, y2, y3, y4Expr, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  set pxR : ℂ := (-(4776) : ℂ) * x ^ 3 + (64038 : ℂ) * x ^ 2 +
    (-(643035 : ℂ) / (2 : ℂ)) * x + ((2240433 : ℂ) / (4 : ℂ))
  set pyR : ℂ := (144 : ℂ) * x ^ 3 + (-(1724) : ℂ) * x ^ 2 + (4515 : ℂ) * x + (624 : ℂ)
  set qxR : ℂ := (-(192) : ℂ) * x ^ 3 + (2044 : ℂ) * x ^ 2 + (39 : ℂ) * x +
    (-(59319 : ℂ) / (4 : ℂ))
  set qyR : ℂ := (-(9120) : ℂ) * x ^ 3 + (158616 : ℂ) * x ^ 2 + (-(962502) : ℂ) * x +
    (2187453 : ℂ)
  have hpx : (24 * x ^ 2 + 344 * x * y1 - 78 * x + 48 * y1 ^ 3 + 12 * y1 ^ 2 - 48 * y1 - 4) = pxR := by
    rw [hy3, hy2]
    simp only [y1, y2, y3, pxR, y4Expr]; ring
  have hpy : (172 * x ^ 2 + 144 * x * y1 ^ 2 + 24 * x * y1 - 48 * x - 936 * y1 ^ 2 - 312) = pyR := by
    rw [hy2]
    simp only [y1, y2, pyR, y4Expr]; ring
  have hqx : (960 * x ^ 2 + 32 * x * y1 + 42 * x - 144 * y1 ^ 2 + 78 * y1 - 612) = qxR := by
    rw [hy2]
    simp only [y1, y2, qxR, y4Expr]; ring
  have hqy : (16 * x ^ 2 - 288 * x * y1 + 78 * x + 192 * y1 ^ 3 + 24 * y1 ^ 2 + 96 * y1 + 8) = qyR := by
    rw [hy3, hy2]
    simp only [y1, y2, y3, qyR, y4Expr]; ring
  set trR : ℂ := (-(13896) : ℂ) * x ^ 3 + (222654 : ℂ) * x ^ 2 +
    (-(2568039 : ℂ) / (2 : ℂ)) * x + ((10990245 : ℂ) / (4 : ℂ))
  set detR : ℂ := (-(4758944) : ℂ) * x ^ 3 + ((239814680 : ℂ) / (9 : ℂ)) * x ^ 2 +
    ((130695070 : ℂ) / (3 : ℂ)) * x + (-(6173061085 : ℂ) / (18 : ℂ))
  set invD : ℂ := ((120762233663457072274298496 : ℂ) / (3725772224909062279719160107502361197 : ℂ)) * x ^ 3 +
    ((355598617178727973098196128 : ℂ) / (3725772224909062279719160107502361197 : ℂ)) * x ^ 2 +
    (-(11117861751405165275958604296 : ℂ) / (3725772224909062279719160107502361197 : ℂ)) * x +
    ((61126596958859574568539946406 : ℂ) / (3725772224909062279719160107502361197 : ℂ))
  set trSq : ℂ := (-(24409512) : ℂ) * x ^ 3 + (94950265 : ℂ) * x ^ 2 +
    (637573461 : ℂ) * x + (-(44493662665 : ℂ) / (16 : ℂ))
  set tauR : ℂ := ((488982824111146060989424571984712 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x ^ 3 +
    (-(6369106137245697634837544458574334 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x ^ 2 +
    ((31497977998540040256547546620809250 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x +
    ((342520331377453525783968856348329819 : ℂ) / (88183957986013308395719765858044052 : ℂ))
  have htr : jacTr x (y4Expr x) = trR := by
    change (24 * x ^ 2 + 344 * x * y1 - 78 * x + 48 * y1 ^ 3 + 12 * y1 ^ 2 - 48 * y1 - 4) +
      (16 * x ^ 2 - 288 * x * y1 + 78 * x + 192 * y1 ^ 3 + 24 * y1 ^ 2 + 96 * y1 + 8) = trR
    rw [hpx, hqy]; simp only [pxR, qyR, trR]; ring
  have hdet : jacDet x (y4Expr x) = detR := by
    change (24 * x ^ 2 + 344 * x * y1 - 78 * x + 48 * y1 ^ 3 + 12 * y1 ^ 2 - 48 * y1 - 4) *
        (16 * x ^ 2 - 288 * x * y1 + 78 * x + 192 * y1 ^ 3 + 24 * y1 ^ 2 + 96 * y1 + 8) -
      (172 * x ^ 2 + 144 * x * y1 ^ 2 + 24 * x * y1 - 48 * x - 936 * y1 ^ 2 - 312) *
        (960 * x ^ 2 + 32 * x * y1 + 42 * x - 144 * y1 ^ 2 + 78 * y1 - 612) = detR
    rw [hpx, hqy, hpy, hqx]
    have hid : pxR * qyR - pyR * qxR - detR =
        ((18917 : ℂ) * x ^ 2 + (-(2639725 : ℂ) / (12 : ℂ)) * x +
          ((20333855 : ℂ) / (36 : ℂ))) * q4Poly x := by
      simp only [pxR, qyR, pyR, qxR, detR, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have hbez : detR * invD = 1 := by
    have hid : (((1964063550276503217127826928 : ℂ) / (29336789172512301415111496909467411 : ℂ)) * x ^ 2 +
        ((4118720136051905910484839876368 : ℂ) / (3725772224909062279719160107502361197 : ℂ)) * x +
        ((102406569887906013795706431526396 : ℂ) / (33531950024181560517472440967521250773 : ℂ))) * q4Poly x +
        detR * invD = 1 := by
      simp only [detR, invD, q4Poly]; ring
    rw [hq, mul_zero, zero_add] at hid; exact hid
  have hdet_ne : jacDet x (y4Expr x) ≠ 0 := by
    rw [hdet]; intro h0; rw [h0, zero_mul] at hbez; exact zero_ne_one hbez
  have htrsq : trR ^ 2 = trSq := by
    have hid : trR ^ 2 - trSq =
        (((335241 : ℂ) / (4 : ℂ)) * x ^ 2 + (-(4317603 : ℂ) / (4 : ℂ)) * x +
          ((27843665 : ℂ) / (8 : ℂ))) * q4Poly x := by
      simp only [trR, trSq, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have htau_eq : trSq * invD = tauR := by
    have hid : trSq * invD - tauR =
        ((-(1279404163088090003109529700388 : ℂ) / (3725772224909062279719160107502361197 : ℂ)) * x ^ 2 +
         (-(46625061169132336209048725911113 : ℂ) / (7451544449818124559438320215004722394 : ℂ)) * x +
         (-(680085595482627001144347005418769 : ℂ) / (29806177799272498237753280860018889576 : ℂ))) * q4Poly x := by
      simp only [trSq, invD, tauR, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have htau : tauRatio (jacTr x (y4Expr x)) (jacDet x (y4Expr x)) = tauR := by
    unfold tauRatio; rw [htr, hdet, htrsq]
    have hdetR_ne : detR ≠ 0 := by rwa [← hdet]
    rw [div_eq_iff hdetR_ne, ← htau_eq]
    calc trSq = trSq * 1 := (mul_one _).symm
      _ = trSq * (detR * invD) := by rw [hbez]
      _ = trSq * invD * detR := by ring
  refine ⟨hdet_ne, ?_⟩
  rw [htau]
  set h0_val : ℂ := (2002873647559254265812683046849380352 : ℂ) * x ^ 3 +
    (-(26087858738158377512294582102320472064) : ℂ) * x ^ 2 +
    (129015717882020004890818750958834688000 : ℂ) * x +
    (-(1928817315884404523539826960845507909632) : ℂ)
  have h0 : (90300372977677627797217040238637109248 : ℂ) * tauR +
      ((-(2279558135214916933942611069746197644288) : ℂ)) = h0_val := by
    simp only [tauR, h0_val]; ring
  set h1_val : ℂ := (-(25193803907298696045444999710051254272) : ℂ) * x ^ 3 +
    (327523374997788989850822751772351314944 : ℂ) * x ^ 2 +
    (-(1617004388466030227045032116554851473408) : ℂ) * x +
    (13528304614998012365139526987136170547520 : ℂ)
  have h1 : h0_val * tauR + ((21580251865599942120239917323725565102528 : ℂ)) = h1_val := by
    have hid : (h0_val * tauR + ((21580251865599942120239917323725565102528 : ℂ))) - h1_val =
        (((425074137379043565458708568109540273491397727496125401398687507456 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x ^ 2 +
         (-(2926109277316007646081994856699651092122161978505688094355782175744 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x +
         ((5691030417346176987865118280679912574598924460577588096775478030464 : ℂ) / (22045989496503327098929941464511013 : ℂ))) * q4Poly x := by
      simp only [h0_val, tauR, h1_val, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  set h2_val : ℂ := (79220928568388691742034506228282457088 : ℂ) * x ^ 3 +
    (-(1027862440721002993087826506184576456448) : ℂ) * x ^ 2 +
    (5065830995074882426407679723958926735584 : ℂ) * x +
    (-(31251386940071098300384598750780822621448) : ℂ)
  have h2 : h1_val * tauR + ((-(90801612796538526687818920091684644325136) : ℂ)) = h2_val := by
    have hid : (h1_val * tauR + ((-(90801612796538526687818920091684644325136) : ℂ))) - h2_val =
        ((-(5346934628773152200284527886777175911426081753865360903024960073216 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x ^ 2 +
         ((36673039387478796861757760769252594711034060565722388011441606718304 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x +
         (-(71165225816480426336250790666201546084579622637370150721013232362168 : ℂ) / (22045989496503327098929941464511013 : ℂ))) * q4Poly x := by
      simp only [h1_val, tauR, h2_val, q4Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have hfinal : h2_val * tauR + ((143276813705244499010518737554045186664681 : ℂ)) = 0 := by
    have hid : h2_val * tauR + ((143276813705244499010518737554045186664681 : ℂ)) =
        (((16813226293436663965271913775018333675528216839951282182371868112864 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x ^ 2 +
         (-(114887807416057229186512987445354090827901838021603136365902402143632 : ℂ) / (22045989496503327098929941464511013 : ℂ)) * x +
         ((222426875447906866413671190802819019755800959030353367711986857840375 : ℂ) / (22045989496503327098929941464511013 : ℂ))) * q4Poly x := by
      simp only [h2_val, tauR, q4Poly]; ring
    rw [hid, hq, mul_zero]
  have hhorner : M4Poly tauR =
      (((((90300372977677627797217040238637109248 : ℂ)) * tauR +
        ((-(2279558135214916933942611069746197644288) : ℂ))) * tauR +
        ((21580251865599942120239917323725565102528 : ℂ))) * tauR +
        ((-(90801612796538526687818920091684644325136) : ℂ))) * tauR +
        ((143276813705244499010518737554045186664681 : ℂ)) := by
    unfold M4Poly; ring
  rw [hhorner, h0, h1, h2]
  exact hfinal

private lemma complex_ofReal_M4 (t : ℝ) : M4Poly (t : ℂ) = ((M4Poly t : ℝ) : ℂ) := by
  unfold M4Poly; push_cast; ring

/-- **Proposition 6.2 (`q₄` Stratum Non-Dicriticality)**: Every complex affine singularity
`(x, y)` of `(P, Q)` (6.2) with `q₄(x) = 0` is non-degenerate (`jacDet x y ≠ 0`) and
satisfies `τ(x, y) ∉ [4, ∞)` (`IsNonDicriticalTau`). -/
theorem prop_6_2_q4_stratum_nondicritical (x y : ℂ)
    (hP : vecP x y = 0) (hQ : vecQ x y = 0) (hq : q4Poly x = 0) :
    jacDet x y ≠ 0 ∧ IsNonDicriticalTau (tauRatio (jacTr x y) (jacDet x y)) := by
  have hy := q4_y_eq x y hP hQ hq
  subst hy
  rcases q4_det_and_M4 x hq with ⟨hdet, hM4⟩
  refine ⟨hdet, ?_⟩
  rintro ⟨him, _⟩
  set τ := tauRatio (jacTr x (y4Expr x)) (jacDet x (y4Expr x))
  have hτ : τ = (τ.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [hτ, complex_ofReal_M4] at hM4
  have hM4_real : M4Poly τ.re = 0 := Complex.ofReal_eq_zero.mp hM4
  have hpos : 0 < M4Poly τ.re := prop_6_2_counterexample_nondicritical.2.2.1 τ.re
  linarith

end LogarithmicRigidity
