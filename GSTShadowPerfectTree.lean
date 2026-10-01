import ErdosTernary2
import GSTShadowSeparationAttack
import GSTUnconditionalCoverage
import GSTGraphV2OmegaWaveLaw
import GSTShadowGapReceipt

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-!
# THE PERFECT BINARY TREE — the shadow's exact local structure

The Shadow Gap counts the survivors globally: exactly `2^L` classes at every
level `L` (`shadow_count_exact`).  This module proves the LOCAL law behind
that count, and pushes the kernel tables two levels deeper.

* **THE LTE UNIT LAW** (`pow4_three_pow_unit`): `4^(3^L) ≡ 1 + 3^(L+1)
  (mod 3^(L+2))` — the LTE coefficient `lteCoeff L` is one modulo three at
  every scale (`lteCoeff_mod3_one`), and this module states the consequence
  in window form.

* **THE CHILD LAWS** (one-liners over the residue module's own green
  machinery): the child `r + t*3^L` agrees with `4^r` on every row `≤ L`
  (`shadow_child_rows`, from `pow4_digit_period`), and its row-`L+1` digit
  is `(digit3 (4^r) (L+1) + t) % 3` (`shadow_child_top`, from
  `pow4_exponent_trit_lift_digit`).

* **THE PERFECT BINARY TREE** (`shadow_two_children`,
  `shadow_perfect_binary_tree`): every surviving class has EXACTLY two
  surviving children at the next level — the survivor tree is the perfect
  binary tree.  The count `2^L` is not just a global accident; it is the
  binary tree law, node by node, forever.

* **THE DEEP TABLES**: the level-six and level-seven kernel receipts —
  `64` surviving classes mod `729 = 3^6` (window seven) and `128` surviving
  classes mod `2187 = 3^7` (window eight), each table decided by the kernel
  over the monolith's own `powMod`.

* **THE DEEP RESIDUAL** (`CombinedResidualDeep`): the campaign's named
  object, shrunk one level — `500 < K`, the full tailF package, and a
  level-six surviving class.  The crown is equivalent to the deep-residual
  firing (`erdos_ternary_2_iff_combined_residual_deep`), every eternal
  shadow lives in the deep residual, and the deep-residual firing is a
  separation supplier.
-/

namespace GSTShadowPerfectTree

open GSTShadowGap
open GSTShadowGapReceipt
open GSTShadowSeparationAttack
open GSTFourPowerDirectResidue

/-! ## Section 1 — the LTE unit law, window form -/

private theorem tpow_succ (k : Nat) : 3^(k+1) = 3 * 3^k := by
  rw [Nat.mul_comm]
  exact Nat.pow_succ 3 k

private theorem tpow_pos (k : Nat) : 0 < 3^k := by positivity

/-- **THE LTE UNIT LAW, WINDOW FORM.**  `4^(3^L) ≡ 1 + 3^(L+1)
(mod 3^(L+2))` — the digit of `4^(3^L)` at row `L+1` is one, at every
scale.  This is `pow4_three_power_lte_exact` plus `lteCoeff_mod3_one`,
packaged for the window calculus. -/
theorem pow4_three_pow_unit (L : Nat) :
    4^(3^L) % 3^(L+2) = 1 + 3^(L+1) := by
  have hlt : 1 + 3^(L+1) < 3^(L+2) := by
    have h1 : 3^(L+2) = 3 * 3^(L+1) := tpow_succ (L+1)
    have hp := tpow_pos (L+1)
    have h3 : 3 ≤ 3^(L+1) := by
      have h1' : 3^(L+1) = 3 * 3^L := tpow_succ L
      have hp' := tpow_pos L
      omega
    omega
  obtain ⟨q, hq⟩ : ∃ q : Nat, lteCoeff L = 3*q + 1 := by
    refine ⟨lteCoeff L / 3, ?_⟩
    have hd := Nat.div_add_mod (lteCoeff L) 3
    have hu := lteCoeff_mod3_one L
    omega
  have hinner : 1 + 3^(L+1) * (3*q + 1) = 1 + 3^(L+1) + 3^(L+2) * q := by
    rw [show 3^(L+2) = 3 * 3^(L+1) from tpow_succ (L+1)]
    ring
  have h := pow4_three_power_lte_exact L
  rw [h, hq, hinner, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## Section 2 — the child laws -/

/-- **THE ROWS LAW.**  The child agrees with the parent on every row `≤ L`:
the lift `t*3^L` is a multiple of `3^p` for every `p ≤ L`, so
`pow4_digit_period` applies row by row. -/
theorem shadow_child_rows (L r t : Nat) (_ht : t < 3)
    (p : Nat) (hp : p ≤ L) :
    digit3 (4^(r + t*3^L)) p = digit3 (4^r) p := by
  have hshift : t * 3^L = 3^p * (t * 3^(L - p)) := by
    rw [show 3^L = 3^p * 3^(L - p) from by
          rw [← Nat.pow_add, show p + (L - p) = L from by omega]]
    ring
  rw [hshift]
  exact pow4_digit_period p r (t * 3^(L - p))

/-- **THE TOP-ROW LAW.**  The child's row-`L+1` digit is the parent's
row-`L+1` digit plus the lift, modulo three.  This is the residue
module's own `pow4_exponent_trit_lift_digit`, stated in child form. -/
theorem shadow_child_top (L r t : Nat) (ht : t < 3) :
    digit3 (4^(r + t*3^L)) (L+1) = (digit3 (4^r) (L+1) + t) % 3 :=
  pow4_exponent_trit_lift_digit L r t ht

/-! ## Section 3 — the perfect binary tree -/

/-- **THE PERFECT BINARY TREE, LOCAL LAW.**  Every surviving class at any
level has exactly two surviving children at the next level: the children
are the two lifts `t` whose row-`L+1` digit `(d + t) % 3` avoids the digit
two, where `d` is the parent's row-`L+1` digit. -/
theorem shadow_two_children (L r : Nat)
    (hclean : ∀ p : Nat, p < L+1 → digit3 (4^r) p ≠ 2) :
    ∃ a b : Nat, a < 3 ∧ b < 3 ∧ a ≠ b ∧
      (∀ p : Nat, p < L+2 → digit3 (4^(r + a*3^L)) p ≠ 2) ∧
      (∀ p : Nat, p < L+2 → digit3 (4^(r + b*3^L)) p ≠ 2) ∧
      (∀ t : Nat, t < 3 →
        (∀ p : Nat, p < L+2 → digit3 (4^(r + t*3^L)) p ≠ 2) → t = a ∨ t = b) := by
  -- survival of the child t ⟺ (d + t) % 3 ≠ 2, where d is the parent's top digit
  have hsurv : ∀ t : Nat, t < 3 →
      ((∀ p : Nat, p < L+2 → digit3 (4^(r + t*3^L)) p ≠ 2)
        ↔ (digit3 (4^r) (L+1) + t) % 3 ≠ 2) := by
    intro t ht
    constructor
    · intro hall
      have hrow := hall (L+1) (by omega)
      rw [shadow_child_top L r t ht] at hrow
      exact hrow
    · intro htop p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · have hp' : p ≤ L := by omega
        rw [shadow_child_rows L r t ht p hp']
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r t ht]
        exact htop
  have hd3 := digit3_lt_three (4^r) (L+1)
  rcases (show digit3 (4^r) (L+1) = 0 ∨ digit3 (4^r) (L+1) = 1
      ∨ digit3 (4^r) (L+1) = 2 by omega) with h0 | h1 | h2
  · refine ⟨0, 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · rw [shadow_child_rows L r 0 (by omega) p (by omega)]
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r 0 (by omega), h0]
        omega
    · intro p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · rw [shadow_child_rows L r 1 (by omega) p (by omega)]
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r 1 (by omega), h0]
        omega
    · intro t ht hall
      have := (hsurv t ht).mp hall
      rw [h0] at this
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
  · refine ⟨0, 2, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · rw [shadow_child_rows L r 0 (by omega) p (by omega)]
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r 0 (by omega), h1]
        omega
    · intro p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · rw [shadow_child_rows L r 2 (by omega) p (by omega)]
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r 2 (by omega), h1]
        omega
    · intro t ht hall
      have := (hsurv t ht).mp hall
      rw [h1] at this
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
      · exact Or.inl rfl
      · omega
      · exact Or.inr rfl
  · refine ⟨1, 2, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · rw [shadow_child_rows L r 1 (by omega) p (by omega)]
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r 1 (by omega), h2]
        omega
    · intro p hp
      rcases (show p < L+1 ∨ p = L+1 by omega) with hple | hpe
      · rw [shadow_child_rows L r 2 (by omega) p (by omega)]
        exact hclean p (by omega)
      · rw [hpe, shadow_child_top L r 2 (by omega), h2]
        omega
    · intro t ht hall
      have := (hsurv t ht).mp hall
      rw [h2] at this
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
      · omega
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- **THE PERFECT BINARY TREE.**  Every surviving class at every level has
exactly two surviving children among its three lifts — and every level-`L+1`
survivor above `r` is one of those two children.  The survivor tree is the
perfect binary tree: `2^L` nodes at level `L`, each node with exactly two
children, doubling forever. -/
theorem shadow_perfect_binary_tree (L r : Nat) (hr : r < 3^L)
    (hclean : ∀ p : Nat, p < L+1 → digit3 (4^r) p ≠ 2) :
    ∃ a b : Nat, a < 3 ∧ b < 3 ∧ a ≠ b ∧
      (r + a*3^L) ∈ survivorClasses (L+1) ∧ (r + b*3^L) ∈ survivorClasses (L+1) ∧
      ∀ r' : Nat, r' < 3^(L+1) → r' % 3^L = r →
        r' ∈ survivorClasses (L+1) → r' = r + a*3^L ∨ r' = r + b*3^L := by
  obtain ⟨a, b, ha, hb, hne, hca, hcb, hall⟩ :=
    shadow_two_children L r hclean
  have hchild (t : Nat) (ht : t < 3)
      (hc : ∀ p : Nat, p < L+2 → digit3 (4^(r + t*3^L)) p ≠ 2) :
      r + t*3^L < 3^(L+1) := by
    have h3 : 3^(L+1) = 3 * 3^L := tpow_succ L
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · omega
    · omega
    · omega
  refine ⟨a, b, ha, hb, hne, ?_, ?_, ?_⟩
  · exact survivorClasses_complete (L+1) (r + a*3^L) (hchild a ha hca) hca
  · exact survivorClasses_complete (L+1) (r + b*3^L) (hchild b hb hcb) hcb
  · intro r' hr' hmod hmem
    have hc := survivorClasses_clean (L+1) r' hr' hmem
    have hsplit : ∃ t : Nat, t < 3 ∧ r' = r + t*3^L := by
      have hrml : r % 3^L < 3^L := Nat.mod_lt r (tpow_pos (L+1))
      have hrm' : r' % 3^L < 3^L := Nat.mod_lt r' (tpow_pos (L+1))
      have hsame : r' % 3^L = r := by omega
      refine ⟨r' / 3^L, ?_, ?_⟩
      · have h3 : 3^(L+1) = 3 * 3^L := tpow_succ L
        rw [h3, Nat.mul_comm] at hr'
        exact Nat.div_lt_of_lt_mul hr'
      · have hdm := Nat.div_add_mod r' (3^L)
        rw [Nat.mul_comm 3^L (r' / 3^L)] at hdm
        omega
    obtain ⟨t, ht, rfl⟩ := hsplit
    have := hall t ht hc
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ## Section 4 — the deep kernel tables -/

/-- The 64 surviving exponent classes modulo `729 = 3^6`, in order. -/
def survivorTable6 : List Nat :=
  [0, 1, 4, 10, 12, 13, 28, 36, 40, 63, 82, 93, 94, 108, 109, 120, 121,
   166, 189, 193, 198, 199, 210, 237, 243, 244, 247, 274, 280, 283, 306,
   318, 324, 325, 336, 363, 364, 372, 387, 415, 432, 436, 441, 442, 444,
   496, 498, 499, 514, 517, 522, 523, 561, 567, 580, 594, 595, 615, 630,
   652, 658, 687, 696, 723]

/-- Decidable membership in the level-six survivor table. -/
def survivor6 (r : Nat) : Bool := survivorTable6.contains r

/-- **THE LEVEL-SIX KERNEL RECEIPT.**  For every class below `729`, the
seven-row window of `4^r` is clean exactly on the exhibited 64-class table. -/
theorem survivor_table6_receipt : ∀ r < 729,
    winClean (powMod 4 r (3^7)) 7 = survivor6 r := by
  decide

/-- The level-six survivor count: exactly `64` classes below `729` have a
clean seven-row window. -/
theorem survivor6_count_receipt :
    (List.range 729).countP (fun r => survivor6 r) = 64 := by
  decide

/-- The level-six killed count: exactly `665` of the `729` classes mod `729`
fail the seven-row window. -/
theorem killed6_count_receipt :
    (List.range 729).countP (fun r => !survivor6 r) = 665 := by
  decide

private theorem digit3_pow_mod_window7 (r p : Nat) (hp : p < 7) :
    digit3 (powMod 4 r (3^7)) p = digit3 (4^r) p := by
  have hpm : powMod 4 r (3^7) = 4^r % 3^7 :=
    powMod_correct 4 r (3^7) (by norm_num)
  rw [hpm]
  exact digit3_mod_window (4^r) 7 p hp

/-- The Bool table agrees with the exhibited survivor list at level six. -/
theorem survivor6_iff_survivorClasses (r : Nat) (hr : r < 729) :
    survivor6 r = true ↔ r ∈ survivorClasses 6 := by
  have h3 : (3:Nat)^6 = 729 := by norm_num
  constructor
  · intro htrue
    have hwin := survivor_table6_receipt r hr
    rw [htrue] at hwin
    have hclean : ∀ p : Nat, p < 7 → digit3 (4^r) p ≠ 2 := by
      intro p hp
      have hdigit := (winClean_iff (powMod 4 r (3^7)) 7).mp hwin p hp
      rw [digit3_pow_mod_window7 r p hp] at hdigit
      exact hdigit
    exact survivorClasses_complete 6 r (by rw [h3]; exact hr) hclean
  · intro hmem
    have hclean := survivorClasses_clean 6 r (by rw [h3]; exact hr) hmem
    have hwin : winClean (powMod 4 r (3^7)) 7 = true := by
      refine (winClean_iff (powMod 4 r (3^7)) 7).mpr ?_
      intro p hp
      have hdigit := hclean p (by omega)
      rw [digit3_pow_mod_window7 r p hp]
      exact hdigit
    have htable := survivor_table6_receipt r hr
    rw [hwin] at htable
    exact htable.symm

/-- **THE LEVEL-SIX SEPARATION.**  Any exponent whose class mod `729` is one
of the `665` killed classes owns a ternary digit two within the first seven
rows. -/
theorem separation_level_six (m : Nat)
    (hkill : survivor6 (m % 729) = false) :
    ∃ p : Nat, p < 7 ∧ digit3 (4^m) p = 2 := by
  have hr : m % 729 < 729 := Nat.mod_lt _ (by norm_num)
  have hne : ¬ ((m % 729) ∈ survivorClasses 6) := by
    intro hmem
    rw [(survivor6_iff_survivorClasses _ hr).mpr hmem] at hkill
    exact Bool.noConfusion hkill
  have hgen := killed_class_early_digit_two 6 m (by
    rw [show (3:Nat)^6 = 729 from by norm_num]
    exact hne)
  obtain ⟨p, hp, hdigit⟩ := hgen
  exact ⟨p, by omega, hdigit⟩

/-- **THE LEVEL-SIX REACH.**  Every exponent either sits in one of the 64
surviving classes mod `729` or is separated with an early digit two. -/
theorem level_six_reach (m : Nat) :
    survivor6 (m % 729) = true ∨
    ∃ p : Nat, p < 7 ∧ digit3 (4^m) p = 2 := by
  cases hb : survivor6 (m % 729) with
  | true => exact Or.inl rfl
  | false => exact Or.inr (separation_level_six m hb)

/-- The 128 surviving exponent classes modulo `2187 = 3^7`, in order. -/
def survivorTable7 : List Nat :=
  [0, 1, 4, 12, 13, 36, 40, 63, 82, 93, 94, 109, 120, 121, 166, 189, 193,
   237, 244, 247, 280, 283, 318, 324, 325, 364, 387, 432, 436, 441, 496,
   514, 522, 523, 567, 580, 594, 595, 615, 630, 687, 696, 729, 730, 733,
   739, 741, 757, 792, 822, 823, 837, 838, 849, 850, 922, 927, 928, 939,
   966, 972, 973, 976, 1003, 1009, 1035, 1047, 1065, 1092, 1093, 1101,
   1144, 1161, 1165, 1171, 1173, 1225, 1227, 1228, 1243, 1246, 1251,
   1252, 1290, 1296, 1359, 1381, 1387, 1452, 1468, 1471, 1486, 1494,
   1498, 1540, 1566, 1624, 1647, 1656, 1657, 1668, 1701, 1732, 1741,
   1764, 1782, 1783, 1794, 1821, 1830, 1845, 1873, 1899, 1900, 1902,
   1956, 1957, 1975, 2019, 2038, 2052, 2053, 2073, 2110, 2116, 2145,
   2154, 2181]

/-- Decidable membership in the level-seven survivor table. -/
def survivor7 (r : Nat) : Bool := survivorTable7.contains r

/-- **THE LEVEL-SEVEN KERNEL RECEIPT.**  For every class below `2187`, the
eight-row window of `4^r` is clean exactly on the exhibited 128-class table. -/
theorem survivor_table7_receipt : ∀ r < 2187,
    winClean (powMod 4 r (3^8)) 8 = survivor7 r := by
  decide

/-- The level-seven survivor count: exactly `128` classes below `2187` have
a clean eight-row window. -/
theorem survivor7_count_receipt :
    (List.range 2187).countP (fun r => survivor7 r) = 128 := by
  decide

/-- The level-seven killed count: exactly `2059` of the `2187` classes mod
`2187` fail the eight-row window. -/
theorem killed7_count_receipt :
    (List.range 2187).countP (fun r => !survivor7 r) = 2059 := by
  decide

private theorem digit3_pow_mod_window8 (r p : Nat) (hp : p < 8) :
    digit3 (powMod 4 r (3^8)) p = digit3 (4^r) p := by
  have hpm : powMod 4 r (3^8) = 4^r % 3^8 :=
    powMod_correct 4 r (3^8) (by norm_num)
  rw [hpm]
  exact digit3_mod_window (4^r) 8 p hp

/-- The Bool table agrees with the exhibited survivor list at level seven. -/
theorem survivor7_iff_survivorClasses (r : Nat) (hr : r < 2187) :
    survivor7 r = true ↔ r ∈ survivorClasses 7 := by
  have h3 : (3:Nat)^7 = 2187 := by norm_num
  constructor
  · intro htrue
    have hwin := survivor_table7_receipt r hr
    rw [htrue] at hwin
    have hclean : ∀ p : Nat, p < 8 → digit3 (4^r) p ≠ 2 := by
      intro p hp
      have hdigit := (winClean_iff (powMod 4 r (3^8)) 8).mp hwin p hp
      rw [digit3_pow_mod_window8 r p hp] at hdigit
      exact hdigit
    exact survivorClasses_complete 7 r (by rw [h3]; exact hr) hclean
  · intro hmem
    have hclean := survivorClasses_clean 7 r (by rw [h3]; exact hr) hmem
    have hwin : winClean (powMod 4 r (3^8)) 8 = true := by
      refine (winClean_iff (powMod 4 r (3^8)) 8).mpr ?_
      intro p hp
      have hdigit := hclean p (by omega)
      rw [digit3_pow_mod_window8 r p hp]
      exact hdigit
    have htable := survivor_table7_receipt r hr
    rw [hwin] at htable
    exact htable.symm

/-- **THE LEVEL-SEVEN SEPARATION.**  Any exponent whose class mod `2187` is
one of the `2059` killed classes owns a ternary digit two within the first
eight rows. -/
theorem separation_level_seven (m : Nat)
    (hkill : survivor7 (m % 2187) = false) :
    ∃ p : Nat, p < 8 ∧ digit3 (4^m) p = 2 := by
  have hr : m % 2187 < 2187 := Nat.mod_lt _ (by norm_num)
  have hne : ¬ ((m % 2187) ∈ survivorClasses 7) := by
    intro hmem
    rw [(survivor7_iff_survivorClasses _ hr).mpr hmem] at hkill
    exact Bool.noConfusion hkill
  have hgen := killed_class_early_digit_two 7 m (by
    rw [show (3:Nat)^7 = 2187 from by norm_num]
    exact hne)
  obtain ⟨p, hp, hdigit⟩ := hgen
  exact ⟨p, by omega, hdigit⟩

/-- **THE LEVEL-SEVEN REACH.**  Every exponent either sits in one of the 128
surviving classes mod `2187` or is separated with an early digit two. -/
theorem level_seven_reach (m : Nat) :
    survivor7 (m % 2187) = true ∨
    ∃ p : Nat, p < 8 ∧ digit3 (4^m) p = 2 := by
  cases hb : survivor7 (m % 2187) with
  | true => exact Or.inl rfl
  | false => exact Or.inr (separation_level_seven m hb)

/-! ## Section 5 — the deep residual -/

/-- **THE DEEP RESIDUAL.**  The campaign's named object, one level deeper:
above the kernel base, the full tailF package, and a level-six surviving
class. -/
def CombinedResidualDeep (K : Nat) : Prop :=
  500 < K ∧ GSTGraphV2OmegaWaveLaw.omegaShadowTailF K ∧
    survivor6 (K % 729) = true

/-- **THE CROWN, EQUIVALENT TO THE DEEP RESIDUAL.**  The full unconditional
statement holds if and only if every deep-residual exponent owns a ternary
digit two. -/
theorem erdos_ternary_2_iff_combined_residual_deep :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ↔
      (∀ K : Nat, CombinedResidualDeep K → ∃ p : Nat, (4^K)/3^p % 3 = 2) := by
  constructor
  · intro hCrown K hK
    obtain ⟨h500, _, _⟩ := hK
    have hn18 : 9 ≤ 2 * K := by omega
    have h2n : noTernaryTwo (2 ^ (2 * K)) = false := hCrown (2 * K) hn18
    have h4eq : 2 ^ (2 * K) = 4 ^ K := by
      rw [show (4 : Nat) = 2 ^ 2 from by decide, Nat.pow_mul]
    rw [h4eq] at h2n
    obtain ⟨p, hp⟩ := no_two_false_digit_witness (4 ^ K) h2n
    exact ⟨p, hp⟩
  · intro hRes n hn
    by_cases hodd : n % 2 = 1
    · exact erdos_ternary_2_odd_universal n hn hodd
    · have h4eq : 2 ^ n = 4 ^ (n / 2) := by
        have hn_eq : n = 2 * (n / 2) := by omega
        rw [show (4 : Nat) = 2 ^ 2 from by decide, ← Nat.pow_mul, ← hn_eq]
      rw [h4eq]
      refine has_two_imp_not_no_two (4 ^ (n / 2)) ?_
      by_cases h500 : n / 2 ≤ 500
      · exact modular_check_base (n / 2) (by omega) h500
      · have hK8 : 8 ≤ n / 2 := by omega
        rcases GSTGraphV2OmegaWaveLaw.omega_digit_two_cases (n / 2) hK8 with
          hShadow | ⟨p, hp⟩
        · rcases GSTUnconditionalCoverage.shadow_split_of_gates (n / 2) hK8 hShadow with
            hT | ⟨p, hp⟩
          · by_cases hs6 : survivor6 (n / 2 % 729) = true
            · obtain ⟨p, hp⟩ := hRes (n / 2) ⟨by omega, hT, hs6⟩
              exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
            · have hkill : survivor6 (n / 2 % 729) = false := by
                cases hh : survivor6 (n / 2 % 729) with
                | true => exact absurd hh hs6
                | false => rfl
              obtain ⟨p, _, hp⟩ := separation_level_six (n / 2) hkill
              exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
          · exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
        · exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp

/-- Every eternal shadow from five on is a deep-residual exponent. -/
theorem eternally_shadowed_deep (m : Nat) (hm : 5 ≤ m)
    (hE : GSTShadowGapReceipt.EternallyShadowed m) :
    CombinedResidualDeep m := by
  have hbase : 500 < m := by
    by_contra h500
    have hle : m ≤ 500 := by omega
    obtain ⟨q, hq, _⟩ :=
      hasTernaryTwo_first_pos (4 ^ m) (modular_check_base m hm hle)
    exact hE q q (Nat.lt_succ_self q) hq
  refine ⟨hbase, ?_, ?_⟩
  · have hK8 : 8 ≤ m := by omega
    rcases GSTGraphV2OmegaWaveLaw.omega_digit_two_cases m hK8 with
      hShadow | ⟨p, hp⟩
    · rcases GSTUnconditionalCoverage.shadow_split_of_gates m hK8 hShadow with
        hT | ⟨p, hp⟩
      · exact hT
      · exact absurd hp (hE p p (Nat.lt_succ_self p))
    · exact absurd hp (hE p p (Nat.lt_succ_self p))
  · rcases level_six_reach m with hs | ⟨p, _, hp⟩
    · exact hs
    · exact absurd hp (hE p p (Nat.lt_succ_self p))

/-- **THE DEEP-RESIDUAL FIRING IS A SEPARATION SUPPLIER.**  If every
deep-residual exponent owns a ternary digit two, then no exponent from five
on is eternally shadowed. -/
theorem separation_of_deep_firing
    (h : ∀ K : Nat, CombinedResidualDeep K → ∃ p : Nat, (4^K)/3^p % 3 = 2) :
    ∀ m : Nat, 5 ≤ m → ¬ GSTShadowGapReceipt.EternallyShadowed m := by
  intro m hm hE
  obtain ⟨p, hp⟩ := h m (eternally_shadowed_deep m hm hE)
  exact hE p p (Nat.lt_succ_self p) hp

/-! ## Section 6 — receipts -/

#print axioms pow4_three_pow_unit
#print axioms shadow_child_rows
#print axioms shadow_child_top
#print axioms shadow_two_children
#print axioms shadow_perfect_binary_tree
#print axioms survivor_table6_receipt
#print axioms survivor6_count_receipt
#print axioms killed6_count_receipt
#print axioms separation_level_six
#print axioms level_six_reach
#print axioms survivor_table7_receipt
#print axioms survivor7_count_receipt
#print axioms killed7_count_receipt
#print axioms separation_level_seven
#print axioms level_seven_reach
#print axioms erdos_ternary_2_iff_combined_residual_deep
#print axioms eternally_shadowed_deep
#print axioms separation_of_deep_firing

end GSTShadowPerfectTree
