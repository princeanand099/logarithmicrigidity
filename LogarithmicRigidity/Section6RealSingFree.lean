/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import LogarithmicRigidity.CaseRNonZero
import LogarithmicRigidity.CounterexampleCert
import LogarithmicRigidity.Section6ElimCert

/-!
# Section 6 (Real Singularity-Free Certification on the 2-Nodal Quartic)

Proves directly on top of Mathlib `v4.35.0` that no real point on the 2-nodal quartic
`f(x, y) = 0` (6.1) is a singularity of the degree-3 vector field `(P, Q)` (6.2),
connecting `sing_PQ_elim` (`x = 0 ∨ q₄(x) = 0 ∨ q₆(x) = 0`) across all three strata:
- `x = 0`: impossible since `f(0, y) > 0` for all `y ∈ ℝ` (`lemma_6_1_quartic_geometry`).
- `q₄(x) = 0`: impossible since `q₄(x) > 0` for all `x ∈ ℝ` (`prop_6_2_counterexample_nondicritical`).
- `q₆(x) = 0`: eliminated via the 3-step linear `y`-relation `A_lin(x) y + B_lin(x) = 0`,
  the unique Gröbner relation `y = y₆(x) (mod q₆)`, and the Bézout coprimality
  `gcd(q₆(x), f(x, y₆(x))) = 1`.
-/

namespace LogarithmicRigidity

set_option maxHeartbeats 800000

private def linA (x : ℂ) : ℂ :=
  1821312 * x ^ 5 - 23036448 * x ^ 4 + 104728664 * x ^ 3 - 116008732 * x ^ 2 -
    248369187 * x + 328945695

private def linB (x : ℂ) : ℂ :=
  46080 * x ^ 6 + 316128 * x ^ 5 - 9313592 * x ^ 4 + 54454966 * x ^ 3 -
    116314829 * x ^ 2 - 89704058 * x + 221114400

private noncomputable def y6Expr (x : ℂ) : ℂ :=
  ((2 : ℂ) / 14821289915489007) *
    (43460908062720000 * x ^ 5 + 25719179549745520 * x ^ 4 -
      177703134828928512 * x ^ 3 - 87621106272103745 * x ^ 2 +
      177383090287728879 * x + 71671677347640944)

private lemma sing_PQ_linear_y (x y : ℂ) (hP : vecP x y = 0) (hQ : vecQ x y = 0)
    (hx : x ≠ 0) (hx13 : 2 * x - 13 ≠ 0) :
    linA x * y + linB x = 0 := by
  let R1 : ℂ := (2 * x - 13) * vecQ x y - 2 * y * vecP x y
  let R2 : ℂ := (x + 13) * vecP x y + 3 * (2 * x - 13) * R1
  let R3a : ℂ := (-x * (4 * x - 13) * (79 * x - 515)) * vecP x y - (2 * (2 * x - 13)) * y * R2
  let R3 : ℂ := (-3 * (4 * x - 13) * (79 * x - 515)) * R3a -
    (-96 * x ^ 4 - 28 * x ^ 3 + 12103 * x ^ 2 - 88114 * x + 240825) * R2
  have hR1 : R1 = 0 := by simp [R1, hP, hQ]
  have hR2 : R2 = 0 := by simp [R2, hP, hR1]
  have hR3a : R3a = 0 := by simp [R3a, hP, hR2]
  have hR3 : R3 = 0 := by simp [R3, hR3a, hR2]
  have hid : R3 = 2 * x * (2 * x - 13) ^ 2 * (linA x * y + linB x) := by
    simp only [R3, R3a, R2, R1, vecP, vecQ, linA, linB]
    ring
  rw [hid] at hR3
  have hfac : 2 * x * (2 * x - 13) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hx) (pow_ne_zero 2 hx13)
  exact (mul_eq_zero.mp hR3).resolve_left hfac

private lemma q6_y_eq (x y : ℂ) (hP : vecP x y = 0) (hQ : vecQ x y = 0) (hq : q6Poly x = 0) :
    y = y6Expr x := by
  have hx : x ≠ 0 := by
    intro h0; subst h0; unfold q6Poly at hq; norm_num at hq
  have hx13 : 2 * x - 13 ≠ 0 := by
    intro h0
    have hxval : x = 13 / 2 := by linear_combination h0 / 2
    rw [hxval] at hq
    unfold q6Poly at hq
    norm_num at hq
  have hlin := sing_PQ_linear_y x y hP hQ hx hx13
  have hlin6 : linA x * y6Expr x + linB x = 0 := by
    have hid : linA x * y6Expr x + linB x =
        (((277063288899840 : ℂ) / 159368708768699) * x ^ 4 +
         (-(107250471431597504 : ℂ) / 4940429971829669) * x ^ 3 +
         ((1473414127449977344 : ℂ) / 14821289915489007) * x ^ 2 +
         (-(655719035056333412 : ℂ) / 4940429971829669) * x +
         (-(365989394789945315 : ℂ) / 4940429971829669)) * q6Poly x := by
      simp only [linA, linB, y6Expr, q6Poly]; ring
    rw [hid, hq, mul_zero]
  have hA_ne : linA x ≠ 0 := by
    have hbez :
        (((3917316482264828894961706246019825194682803752491153058688 : ℂ) /
            85007652736346587210826196933929389616874448661423221079780273349) * x ^ 4 +
         (-(12113358087572590058019231213099353706049023479108440051060000 : ℂ) /
            23717135113440697831820508944566299703107971176537078681258696264371) * x ^ 3 +
         ((128121619639986903941565994018857174068308333067571634027797896 : ℂ) /
            71151405340322093495461526833698899109323913529611236043776088793113) * x ^ 2 +
         ((4156664570054669587638212886016900336861432166303105845304900 : ℂ) /
            7905711704480232610606836314855433234369323725512359560419565421457) * x +
         (-(15651049291994713456246002121834821320990568447145445365419079 : ℂ) /
            1824395008726207525524654534197407669469843936656698360096822789567)) * q6Poly x +
        ((-(3686886100955133077611017643312776653819109414109320525824000 : ℂ) /
            23717135113440697831820508944566299703107971176537078681258696264371) * x ^ 5 +
         (-(22070691028315529732060236360862212346060497918315254179655952 : ℂ) /
            71151405340322093495461526833698899109323913529611236043776088793113) * x ^ 4 +
         ((152131574873848519097641457703637132264281577164317841888544 : ℂ) /
            255022958209039761632478590801788168850623345984269663239340820047) * x ^ 3 +
         ((86733187928512848087940580466053048496966841840358548969797620 : ℂ) /
            71151405340322093495461526833698899109323913529611236043776088793113) * x ^ 2 +
         (-(4564081412279571468747578184487133161891829752917523471968785 : ℂ) /
            7905711704480232610606836314855433234369323725512359560419565421457) * x +
         (-(6539292528700066060671146257218220744906489705598208090661853 : ℂ) /
            5473185026178622576573963602592223008409531809970095080290468368701)) * linA x = 1 := by
      simp only [q6Poly, linA]; ring
    intro h0
    rw [hq, h0, mul_zero, mul_zero, add_zero] at hbez
    exact zero_ne_one hbez
  have hdiff : linA x * (y - y6Expr x) = 0 := by linear_combination hlin - hlin6
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hA_ne)

private lemma q6_quartic_ne_zero (x : ℂ) (hq : q6Poly x = 0) :
    quarticF x (y6Expr x) ≠ 0 := by
  set y1 : ℂ := y6Expr x
  set y2 : ℂ :=
    ((50663505389056000 : ℂ) / 14821289915489007) * x ^ 5 +
    ((169604470717392788 : ℂ) / 44463869746467021) * x ^ 4 +
    (-(2122945618829120 : ℂ) / 159368708768699) * x ^ 3 +
    (-(539603456364099352 : ℂ) / 44463869746467021) * x ^ 2 +
    ((63289934789820016 : ℂ) / 4940429971829669) * x +
    ((400908575371651072 : ℂ) / 44463869746467021)
  set y4 : ℂ :=
    (-(284508579678080000 : ℂ) / 133391609239401063) * x ^ 5 +
    (-(686383294660615465 : ℂ) / 400174827718203189) * x ^ 4 +
    ((23360948997929603 : ℂ) / 2868636757836582) * x ^ 3 +
    ((39859912320087797285 : ℂ) / 6402797243491251024) * x ^ 2 +
    (-(1351265480920908737 : ℂ) / 177855478985868084) * x +
    (-(2196766214414418992 : ℂ) / 400174827718203189)
  have hy2 : y1 ^ 2 = y2 := by
    have hid : y1 ^ 2 - y2 =
        (((409906798966189301964800000 : ℂ) / 73223544919658712086722645948683) * x ^ 4 +
         ((926024225612408482061310400 : ℂ) / 219670634758976136260167937846049) * x ^ 3 +
         (-(2795188882542953108682047680 : ℂ) / 219670634758976136260167937846049) * x ^ 2 +
         (-(2237968419279160735661541016 : ℂ) / 219670634758976136260167937846049) * x +
         (-(404240508316699660173874892 : ℂ) / 219670634758976136260167937846049)) * q6Poly x := by
      simp only [y1, y2, y6Expr, q6Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have hy4 : y1 ^ 4 = y4 := by
    have hpow : y1 ^ 4 = (y1 ^ 2) ^ 2 := by ring
    rw [hpow, hy2]
    have hid : y2 ^ 2 - y4 =
        (((1253315809720169118127232000 : ℂ) / 659011904276928408780503813538147) * x ^ 4 +
         ((6772638364669522415732911711 : ℂ) / 1977035712830785226341511440614441) * x ^ 3 +
         (-(5435468170098296019923527483 : ℂ) / 1977035712830785226341511440614441) * x ^ 2 +
         (-(44220025393084989549842170633 : ℂ) / 7908142851323140905366045762457764) * x +
         (-(59771538103886920511119848179 : ℂ) / 31632571405292563621464183049831056)) * q6Poly x := by
      simp only [y2, y4, q6Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  set fR : ℂ :=
    ((1062656388816128000 : ℂ) / 133391609239401063) * x ^ 5 +
    ((1076507183866214272 : ℂ) / 400174827718203189) * x ^ 4 +
    (-(93735749707545521 : ℂ) / 2868636757836582) * x ^ 3 +
    (-(25539095941512130543 : ℂ) / 3201398621745625512) * x ^ 2 +
    ((3081276680902586227 : ℂ) / 88927739492934042) * x +
    (-(348361548511753846 : ℂ) / 400174827718203189)
  have hf : quarticF x (y6Expr x) = fR := by
    change 2 * x ^ 4 + x ^ 3 - 2 * x ^ 2 * y1 ^ 2 + x ^ 2 * y1 - 8 * x ^ 2 +
      2 * y1 ^ 4 + 4 * y1 ^ 2 + 2 = fR
    rw [hy4, hy2]
    have hid : (2 * x ^ 4 + x ^ 3 - 2 * x ^ 2 * y2 + x ^ 2 * y1 - 8 * x ^ 2 +
        2 * y4 + 4 * y2 + 2) - fR =
        ((-(14067572903 : ℂ) / 88927739492934042) * x +
         (-(54130458157 : ℂ) / 88927739492934042)) * q6Poly x := by
      simp only [y1, y2, y4, fR, y6Expr, q6Poly]; ring
    exact sub_eq_zero.mp (by rw [hid, hq, mul_zero])
  have hbez :
      (((738539746670019599697218853131548785172515462860747264000 : ℂ) /
          1440246713212506416632736312710529648103845786119542969303855033) * x ^ 4 +
       ((2703872455721786386328903328678438424295006295717141767936 : ℂ) /
          4320740139637519249898208938131588944311537358358628907911565099) * x ^ 3 +
       (-(1332370171129373827958568153173289544711536485845151456723 : ℂ) /
          1178383674446596159063147892217706075721328370461444247612245027) * x ^ 2 +
       (-(18876133513045184701028283988671386843867204630280445459504 : ℂ) /
          12962220418912557749694626814394766832934612075075886723734695297) * x +
       ((120024648336896528744483404895986061005857675718966214963 : ℂ) /
          7681315803800034222041260334456158123220510859304229169620560176)) * q6Poly x +
      ((-(12810128235136621533520162908964664967254016000 : ℂ) /
          32391393763628603886425497952539079607094012573) * x ^ 5 +
       (-(16822374739251722341236367275003553547894439456 : ℂ) /
          32391393763628603886425497952539079607094012573) * x ^ 4 +
       ((1611545142074665580105266939274453004617424472 : ℂ) /
          1044883669794471093110499933952873535712710083) * x ^ 3 +
       ((62829976628347012337470378620340970190897730352 : ℂ) /
          32391393763628603886425497952539079607094012573) * x ^ 2 +
       (-(1340332501828084404007000346308339666790551700 : ℂ) /
          875443074692664969903391836555110259651189529) * x +
       (-(9832799744219912581776499994000513428205602095 : ℂ) /
          4983291348250554444065461223467550708783694242)) * fR = 1 := by
    simp only [fR, q6Poly]; ring
  rw [hq, mul_zero, zero_add] at hbez
  rw [hf]
  intro h0
  rw [h0, mul_zero] at hbez
  exact zero_ne_one hbez

private lemma complex_ofReal_q4 (t : ℝ) : q4Poly (t : ℂ) = ((q4Poly t : ℝ) : ℂ) := by
  unfold q4Poly; push_cast; ring

private lemma complex_ofReal_vecP (x y : ℝ) : vecP (x : ℂ) (y : ℂ) = ((vecP x y : ℝ) : ℂ) := by
  unfold vecP; push_cast; ring

private lemma complex_ofReal_vecQ (x y : ℝ) : vecQ (x : ℂ) (y : ℂ) = ((vecQ x y : ℝ) : ℂ) := by
  unfold vecQ; push_cast; ring

private lemma complex_ofReal_quarticF (x y : ℝ) :
    quarticF (x : ℂ) (y : ℂ) = ((quarticF x y : ℝ) : ℂ) := by
  unfold quarticF; push_cast; ring

/-- **Proposition 6.2 (No Real Singularities on the Quartic)**: Neither real oval of the
2-nodal quartic `f(x, y) = 0` (6.1) contains any singularity of `(P, Q)` (6.2). -/
theorem prop_6_2_no_real_singularity_on_quartic (x y : ℝ)
    (hf : quarticF x y = 0) : ¬ (vecP x y = 0 ∧ vecQ x y = 0) := by
  rintro ⟨hP, hQ⟩
  have hPc : vecP (x : ℂ) (y : ℂ) = 0 := by rw [complex_ofReal_vecP, hP]; simp
  have hQc : vecQ (x : ℂ) (y : ℂ) = 0 := by rw [complex_ofReal_vecQ, hQ]; simp
  have hfc : quarticF (x : ℂ) (y : ℂ) = 0 := by rw [complex_ofReal_quarticF, hf]; simp
  rcases sing_PQ_elim (x : ℂ) (y : ℂ) hPc hQc with hx0 | hq4 | hq6
  · have hxR : x = 0 := Complex.ofReal_eq_zero.mp hx0
    subst hxR
    have hpos : 0 < quarticF (0 : ℝ) y := lemma_6_1_quartic_geometry.2.2.1 y
    linarith
  · rw [complex_ofReal_q4] at hq4
    have hq4R : q4Poly x = 0 := Complex.ofReal_eq_zero.mp hq4
    have hpos : 0 < q4Poly x := prop_6_2_counterexample_nondicritical.2.1 x
    linarith
  · have hy := q6_y_eq (x : ℂ) (y : ℂ) hPc hQc hq6
    rw [hy] at hfc
    exact q6_quartic_ne_zero (x : ℂ) hq6 hfc

end LogarithmicRigidity
