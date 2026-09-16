import Mathlib
import GSTTowerFire
import GSTTheActConstruction
import GSTFourPowerDirectResidue

open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTTheActConstruction (feedback_fire_of_class cantorian_dust_mod_729)
open GSTFourPowerDirectResidue (digit3_eq_of_mod_next)

namespace GSTWorldtraceArithmetic

set_option maxHeartbeats 2000000

/-!
# THE WORLDTRACE ARITHMETIC — the boss's transformation, landed

The stuck gap (GAP-A2, the c_infinity blade survivor tree) TRANSFORMED
into worldtrace arithmetic and attacked there.  The transformation:

    4^(1+3m) = 4 * 64^m = 4 * (1+63)^m = 4 * SUM_i C(m,i) * 63^i

Every dust power is a BINOMIAL SUM in the exponent's half-scale — and
every deep row becomes an EXPLICIT POLYNOMIAL in m with 3-adic
coefficients 4*7^i sitting at row-blocks 2i:

  * row five  = the QUADRATIC blade `4 + 252m + 15876*C(m,2)` mod 729
  * row seven = the CUBIC blade `4 + 252m + 15876*C(m,2) + 1000188*C(m,3)`
    mod 6561

Machine receipts BEFORE landing (this session, exact big-int / modular,
`/tmp/wt_receipts.py`):

  * R1 32/32 — the level-6 dead classes mod 2187 all fire at row seven
    (modular 4^rho mod 3^8 arithmetic); survivors double 32 -> 64 exactly.
  * R2 the quadratic blade's kill set CONTAINS the entire green row-five
    table {85, 91, 112, 118, 163, 175, 190, 202} — the polynomial
    reproduces the machine's green cascade.
  * R4 the cubic identity holds 0 failures on 0 <= m < 6561 step 7, and
    row-seven polynomial reads match direct computation 2187/2187.

Sections:

  * SS1 THE BINOMIAL LADDER — `one_add_pow_three_term`,
    `one_add_pow_four_term` (the two-term `GSTTowerFire` engine extended).
  * SS2 THE TRANSFORMATION — `wt_rebase`, `wt_quad_mod729` (the
    quadratic blade), `wt_cubic_mod6561` (the cubic blade).
  * SS3 THE READS — `wt_row_five_read`, `wt_row_seven_read`: the dust
    power's deep rows ARE the polynomial blades, plus the polynomial
    kill demo (`wt_quad_fire_demo`: the quadratic kills K = 85 at row
    five without ever computing 4^85).
  * SS4 THE SIXTH CASCADE LEVEL — `fire_of_mod2187`, `dust_fire_row_seven`
    (32 dead classes), `no22_of_cascade_six`, `cantorian_dust_mod_2187`
    (the 64-survivor map).
-/

/-! ## §1 The binomial ladder -/

/-- **Choose-one, by induction** (self-contained: only
`Nat.choose_succ_succ` and `Nat.choose_zero_right`). -/
theorem wt_choose_one (n : Nat) : Nat.choose n 1 = n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h : Nat.choose (k+1) 1 = Nat.choose k 0 + Nat.choose k 1 :=
      Nat.choose_succ_succ k 0
    rw [h, Nat.choose_zero_right, ih]
    omega

/-- **The three-term binomial ladder.** `(1+x)^j` with the first three
orders explicit — the term structure the worldtrace window reads. -/
theorem one_add_pow_three_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x + x*x*x*R := by
  induction j with
  | zero =>
    have h0 : Nat.choose 0 2 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h0]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    rw [Nat.pow_succ, hR, hc]
    refine ⟨Nat.choose j 2 + R + x*R, ?_⟩
    ring

/-- **The four-term binomial ladder.**  One order deeper: the cubic
window's engine. -/
theorem one_add_pow_four_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + x*x*x*x*R := by
  induction j with
  | zero =>
    have h02 : Nat.choose 0 2 = 0 := by decide
    have h03 : Nat.choose 0 3 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h02, h03]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=
      Nat.choose_succ_succ j 2
    rw [Nat.pow_succ, hR, hc2, hc3]
    refine ⟨Nat.choose j 3 + R + x*R, ?_⟩
    ring

/-! ## §2 The transformation — the dust as a binomial sum -/

/-- **THE REBASE.**  Every dust power is a power of sixty-four:
`4^(1+3m) = 4 * 64^m` — and 64 = 1 + 63 opens the binomial world. -/
theorem wt_rebase (m : Nat) : 4^(1+3*m) = 4 * 64^m := by
  have h43 : (4:Nat)^3 = 64 := by decide
  rw [Nat.pow_add, Nat.pow_mul, h43, Nat.pow_one]

/-- **THE QUADRATIC BLADE.**  Row-window congruence of the dust power:
`4^(1+3m)` is the quadratic `4 + 252m + 15876*C(m,2)` mod 729 — the
order-two worldtrace.  (63^3 = 250047 = 729*343 dies mod 729.) -/
theorem wt_quad_mod729 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729] := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63 + 63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*R) % 729
     = (4 + 252*m + 15876*Nat.choose m 2) % 729
  have hd : 729 ∣ 1000188*R := by
    refine ⟨1372*R, ?_⟩
    ring
  have hz : 1000188*R % 729 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-- **THE CUBIC BLADE.**  One window deeper: `4^(1+3m)` is the cubic
`4 + 252m + 15876*C(m,2) + 1000188*C(m,3)` mod 6561 — the order-three
worldtrace.  (63^4 = 3^8 * 7^4 dies mod 3^8 = 6561.) -/
theorem wt_cubic_mod6561 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561] := by
  obtain ⟨R, hR⟩ := one_add_pow_four_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63
        + Nat.choose m 3 * 63 * 63 * 63 + 63*63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*R) % 6561
     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) % 6561
  have hd : 6561 ∣ 63011844*R := by
    refine ⟨9604*R, ?_⟩
    ring
  have hz : 63011844*R % 6561 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-! ## §3 The reads — the deep rows ARE the polynomials -/

/-- **ROW FIVE IS THE QUADRATIC.**  For EVERY m: the fifth row of the
dust power `4^(1+3m)` is the fifth row of the quadratic blade — the
worldtrace read, exact. -/
theorem wt_row_five_read (m : Nat) :
    digit3 (4^(1+3*m)) 5 = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5 := by
  have h729 : (3:Nat)^(5+1) = 729 := by decide
  have h := wt_quad_mod729 m
  rw [← h729] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **ROW SEVEN IS THE CUBIC.**  For EVERY m: the seventh row of the
dust power is the seventh row of the cubic blade. -/
theorem wt_row_seven_read (m : Nat) :
    digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7 := by
  have h6561 : (3:Nat)^(7+1) = 6561 := by decide
  have h := wt_cubic_mod6561 m
  rw [← h6561] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **THE POLYNOMIAL KILL DEMO.**  The quadratic blade kills K = 85
(m = 28) at row five WITHOUT EVER COMPUTING `4^85`: the worldtrace
quadratic `4 + 252*28 + 15876*C(28,2) ≡ 499 mod 729` reads digit two
at row five.  The transformed problem, solved in transformed
coordinates. -/
theorem wt_quad_fire_demo : digit3 (4^(1+3*28)) 5 = 2 := by
  rw [wt_row_five_read]
  decide

/-! ## §4 The sixth cascade level — the compression continues -/

/-- **THE UNIFORM KILL, LEVEL-SIX FORM.**  `K ≡ r + 729*t mod 2187`
fires at row seven when the noise receipt holds.  All arithmetic
literal. -/
theorem fire_of_mod2187 (K r t : Nat)
    (hr : r < 729) (ht : t < 3)
    (hnoise : (digit3 (4^r) 7 + t) % 3 = 2)
    (hclass : K % 2187 = r + 729 * t) :
    digit3 (4^K) 7 = 2 := by
  have h2187 : (3:Nat)^(6+1) = 2187 := by decide
  have h729 : (3:Nat)^6 = 729 := by decide
  have hK : K % 3^(6+1) = r + 3^6 * t := by
    rw [h2187, h729]
    exact hclass
  have hr' : r < 3^6 := by
    rw [h729]
    exact hr
  exact feedback_fire_of_class 6 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL SIX (row seven).**  Every exponent in one of the
thirty-two dead classes mod 2187 fires its digit two at row seven.
Generated from the worldtrace noise receipts (`noise_6(r) = digit3 (4^r) 7`,
dead child `t = (2 - noise) % 3`, dead class `r + 729*t`) — the sixth
storey of the feedback tree, each node keeping exactly two alive
children (`unique_dead_child`). -/
theorem dust_fire_row_seven (K : Nat)
    (hK : K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981) :
    digit3 (4^K) 7 = 2 := by
  rcases hK with h10 | h28 | h199 | h274 | h415 | h442 | h499 | h517 | h652 | h658 | h742 | h769 | h811 | h895 | h1012 | h1054 | h1309 | h1324 | h1459 | h1462 | h1552 | h1567 | h1579 | h1651 | h1702 | h1705 | h1738 | h1822 | h1894 | h1954 | h1972 | h1981
  · exact fire_of_mod2187 K 10 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 28 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 199 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 274 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 415 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 442 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 499 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 517 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 652 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 658 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 13 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 40 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 82 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 166 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 283 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 325 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 580 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 595 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 4 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 94 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 109 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 121 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 193 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 244 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 247 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 280 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 364 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 436 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 496 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 514 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 523 2 (by decide) (by decide) (by decide) (by omega)
/-- **THE DUST PINNED AT LEVEL SIX — THE MAP DOUBLES AGAIN.**  A Cantorian
dust exponent (`K ≡ 1 mod 3`) lives in one of SIXTY-FOUR surviving
residues mod 2187.  The structural law, third stroke: `2, 4, 8, 16,
32, 64` — the alive set doubles level by level without exception,
every node keeping exactly two children by the blade's one-of-three. -/
theorem cantorian_dust_mod_2187 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116 := by
  have h729 := cantorian_dust_mod_729 K hd hc
  have hrow := hc 7 (by omega)
  have hd0 : K % 2187 ≠ 10 :=
    fun h => absurd (dust_fire_row_seven K (Or.inl h)) hrow
  have hd1 : K % 2187 ≠ 28 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inl h))) hrow
  have hd2 : K % 2187 ≠ 199 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hd3 : K % 2187 ≠ 274 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hd4 : K % 2187 ≠ 415 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hd5 : K % 2187 ≠ 442 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hd6 : K % 2187 ≠ 499 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hd7 : K % 2187 ≠ 517 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hd8 : K % 2187 ≠ 652 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hd9 : K % 2187 ≠ 658 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hd10 : K % 2187 ≠ 742 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hd11 : K % 2187 ≠ 769 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hd12 : K % 2187 ≠ 811 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hd13 : K % 2187 ≠ 895 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hd14 : K % 2187 ≠ 1012 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hd15 : K % 2187 ≠ 1054 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))) hrow
  have hd16 : K % 2187 ≠ 1309 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) hrow
  have hd17 : K % 2187 ≠ 1324 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))) hrow
  have hd18 : K % 2187 ≠ 1459 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) hrow
  have hd19 : K % 2187 ≠ 1462 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))) hrow
  have hd20 : K % 2187 ≠ 1552 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) hrow
  have hd21 : K % 2187 ≠ 1567 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))) hrow
  have hd22 : K % 2187 ≠ 1579 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) hrow
  have hd23 : K % 2187 ≠ 1651 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))) hrow
  have hd24 : K % 2187 ≠ 1702 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) hrow
  have hd25 : K % 2187 ≠ 1705 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))) hrow
  have hd26 : K % 2187 ≠ 1738 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) hrow
  have hd27 : K % 2187 ≠ 1822 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))) hrow
  have hd28 : K % 2187 ≠ 1894 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) hrow
  have hd29 : K % 2187 ≠ 1954 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))) hrow
  have hd30 : K % 2187 ≠ 1972 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) hrow
  have hd31 : K % 2187 ≠ 1981 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))) hrow
  rcases h729 with h1 | h4 | h10 | h13 | h28 | h40 | h82 | h94 | h109 | h121 | h166 | h193 | h199 | h244 | h247 | h274 | h280 | h283 | h325 | h364 | h415 | h436 | h442 | h496 | h499 | h514 | h517 | h523 | h580 | h595 | h652 | h658 <;> omega

/-- **THE CASCADE KILL, LEVEL SIX.**  The thirty-two new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_six (K : Nat)
    (h : K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 7 (dust_fire_row_seven K h)

/-- **THE LEVEL-SIX RECEIPT.**  The worldtrace transformation assembled:
the binomial ladder, the quadratic and cubic blades, the polynomial
reads, the polynomial kill demo, the uniform engine, the thirty-two
fires, the kill chain, and the doubled survivor map. -/
theorem the_worldtrace_receipt :
    (∀ m : Nat, 4^(1+3*m) = 4 * 64^m) ∧
    (∀ m : Nat, ∃ R : Nat, (1+63)^m
      = 1 + m*63 + Nat.choose m 2 * 63 * 63 + 63*63*63*R) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729]) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561]) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 5
      = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7) ∧
    (digit3 (4^(1+3*28)) 5 = 2) ∧
    (∀ K r t : Nat, r < 729 → t < 3 →
      (digit3 (4^r) 7 + t) % 3 = 2 → K % 2187 = r + 729 * t →
      digit3 (4^K) 7 = 2) ∧
    (∀ K : Nat, K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 → digit3 (4^K) 7 = 2) ∧
    (∀ K : Nat, K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116) :=
  ⟨wt_rebase,
    fun m => one_add_pow_three_term 63 m,
    wt_quad_mod729, wt_cubic_mod6561,
    wt_row_five_read, wt_row_seven_read,
    wt_quad_fire_demo, fire_of_mod2187,
    dust_fire_row_seven, no22_of_cascade_six, cantorian_dust_mod_2187⟩

#print axioms wt_choose_one
#print axioms one_add_pow_three_term
#print axioms one_add_pow_four_term
#print axioms wt_rebase
#print axioms wt_quad_mod729
#print axioms wt_cubic_mod6561
#print axioms wt_row_five_read
#print axioms wt_row_seven_read
#print axioms wt_quad_fire_demo
#print axioms fire_of_mod2187
#print axioms dust_fire_row_seven
#print axioms no22_of_cascade_six
#print axioms cantorian_dust_mod_2187
#print axioms the_worldtrace_receipt

end GSTWorldtraceArithmetic
