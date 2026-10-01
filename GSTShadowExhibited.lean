import GSTShadowPerfectTree
import GSTClimbInfiniteFamily

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# THE EXHIBITED SHADOW SET — the bounded window, the three paid shadows,
# and the sharpest named form of the battle

The separation door states that no exponent `m ≥ 5` is eternally shadowed.
This module pays the finite base of that door and sharpens its statement
to the exact form Erdős named: the clean powers of four are `1, 4, 256`
and no others.

* **THE BOUNDED-WINDOW COLLAPSE** (`eternally_shadowed_iff_bounded_window`):
  when `4^m < 3^B`, the eternal (all-rows) cleanliness of `4^m` is a finite
  check — the first `B` rows.  The eternal condition on a natural exponent
  is never infinitary: above the number itself every row is zero.

* **THE THREE PAID SHADOWS** (`shadow_zero`, `shadow_one`, `shadow_four`):
  the exponents `0, 1, 4` ARE eternally shadowed — the powers
  `4^0 = 1`, `4^1 = 4 = 11₃`, `4^4 = 256 = 100111₃` are clean, each by a
  kernel-decided bounded window.

* **THE FIVE PAID NON-SHADOWS** (`not_shadow_two`, `not_shadow_three`,
  `not_shadow_five`, `not_shadow_six`, `not_shadow_seven`): every other
  exponent below eight fires a digit two (`16 = 121₃`, `64 = 2101₃`,
  `1024 = 1101221₃`, `4096 = 121212101₃`, `16384 = 211110211₃`).

* **THE EXACT SET BELOW EIGHT** (`shadow_below_eight`): the eternally
  shadowed exponents below eight are exactly `0, 1, 4`.

* **THE CANTORIAN BRIDGE** (`eternally_shadowed_iff_cantorian`): the
  shadow predicate of the gap era and the Cantorian predicate of the
  climb era are one object — the campaign's two names for the Erdős
  core are machine-checked interchangeable, and every `cantorian_*`
  theorem of the climb family now reads as a shadow theorem.

* **THE SHARPENED BATTLE** (`shadow_set_iff_exhibited`,
  `crown_of_shadow_set`, `the_one_battle_exhibited`): the comparator's
  unconditional statement is equivalent to the shadow set being exactly
  the three exhibited shadows — the strongest named form the war has
  ever reduced itself to.  The three memberships are paid here; the
  remaining content is the upper bound alone.

* **THE ELEMENT LAW** (`shadow_class_all_levels`, `shadow_is_element`):
  every eternal shadow is a surviving class at every level — and above
  its own size, a surviving list element: the shadow `m` itself sits on
  the exhibited survivor list of every scale `3^L > m`.  The level-seven
  class constraint (`shadow_survivor_seven`) pins any counterexample to
  one of the `128` classes of `survivorTable7`.
-/

namespace GSTShadowExhibited

open GSTFourPowerDirectResidue (digit3)
open GSTShadowGap (digit3_mod_window pow4_mod_window_class)
open GSTShadowGapReceipt
open GSTShadowSeparationAttack
open GSTShadowPerfectTree (survivor7 level_seven_reach)
open GSTClimbInfiniteFamily (CantorianPower cantorian_zero cantorian_one
  cantorian_four not_cantorian_two not_cantorian_three)

/-! ## Section 0 — helpers -/

/-- Every row at or above the number's own ternary size is zero. -/
private theorem digit3_zero_of_lt (R p : Nat) (h : R < 3^p) :
    digit3 R p = 0 := by
  unfold digit3
  rw [Nat.div_eq_of_lt h, Nat.zero_mod]

/-! ## Section 1 — the bounded-window collapse -/

/-- **THE BOUNDED-WINDOW COLLAPSE.**  When `4^m < 3^B`, the eternal
shadow condition on `m` is exactly the cleanliness of the first `B`
rows: every row at or above `B` is zero, so the infinite quantifier
collapses to a finite window.  The eternal condition on a natural
exponent is a bounded check at depth the ternary size of `4^m`. -/
theorem eternally_shadowed_iff_bounded_window (m B : Nat) (hB : 4^m < 3^B) :
    EternallyShadowed m ↔
      (∀ p : Nat, p < B → digit3 (4^m) p ≠ 2) := by
  constructor
  · intro hE p hp
    exact hE B p (by omega)
  · intro hwin L p hp
    rcases Nat.lt_or_ge p B with hlt | hge
    · exact hwin p hlt
    · have hle : 3^B ≤ 3^p := Nat.pow_le_pow_of_le (by decide) hge
      have hlt2 : 4^m < 3^p := by omega
      rw [digit3_zero_of_lt (4^m) p hlt2]
      decide

/-! ## Section 2 — the Cantorian bridge -/

/-- **THE CANTORIAN BRIDGE.**  The gap era's shadow predicate and the
climb era's Cantorian predicate are one object: row zero of every power
of four is one, so the all-rows and from-row-one formulations of the
Erdős core coincide.  Every theorem of the climb family about
`CantorianPower` now reads as a theorem about `EternallyShadowed`, and
conversely. -/
theorem eternally_shadowed_iff_cantorian (m : Nat) :
    EternallyShadowed m ↔ GSTClimbInfiniteFamily.CantorianPower m := by
  constructor
  · intro hE p _hp
    have hraw : 4^m / 3^p % 3 ≠ 2 := hE p p (by omega)
    exact hraw
  · intro hC L p _hp
    cases p with
    | zero =>
        rw [digit3_pow4_zero]
        decide
    | succ q =>
        have hraw : 4^m / 3^(q+1) % 3 ≠ 2 := hC (q + 1) (by omega)
        exact hraw

/-! ## Section 3 — the three paid shadows -/

/-- **THE FIRST PAID SHADOW.**  `4^0 = 1` is clean: the exponent zero is
eternally shadowed. -/
theorem shadow_zero : EternallyShadowed 0 :=
  (eternally_shadowed_iff_bounded_window 0 1 (by decide)).mpr (by decide)

/-- **THE SECOND PAID SHADOW.**  `4^1 = 4 = 11₃` is clean: the exponent
one is eternally shadowed. -/
theorem shadow_one : EternallyShadowed 1 :=
  (eternally_shadowed_iff_bounded_window 1 2 (by decide)).mpr (by decide)

/-- **THE THIRD PAID SHADOW.**  `4^4 = 256 = 100111₃` is clean: the
exponent four is eternally shadowed.  This is Erdős's largest known
clean power of four. -/
theorem shadow_four : EternallyShadowed 4 :=
  (eternally_shadowed_iff_bounded_window 4 6 (by decide)).mpr (by decide)

/-! ## Section 4 — the five paid non-shadows below eight -/

/-- `4^2 = 16 = 121₃` fires at row one: two is not a shadow. -/
theorem not_shadow_two : ¬ EternallyShadowed 2 := by
  intro hE
  have h := (eternally_shadowed_iff_bounded_window 2 3 (by decide)).mp hE
  exact h 1 (by omega) (by decide)

/-- `4^3 = 64 = 2101₃` fires at row three: three is not a shadow. -/
theorem not_shadow_three : ¬ EternallyShadowed 3 := by
  intro hE
  have h := (eternally_shadowed_iff_bounded_window 3 4 (by decide)).mp hE
  exact h 3 (by omega) (by decide)

/-- `4^5 = 1024 = 1101221₃` fires at row two: five is not a shadow. -/
theorem not_shadow_five : ¬ EternallyShadowed 5 := by
  intro hE
  have h := (eternally_shadowed_iff_bounded_window 5 7 (by decide)).mp hE
  exact h 2 (by omega) (by decide)

/-- `4^6 = 4096 = 121212101₃` fires at row two: six is not a shadow. -/
theorem not_shadow_six : ¬ EternallyShadowed 6 := by
  intro hE
  have h := (eternally_shadowed_iff_bounded_window 6 8 (by decide)).mp hE
  exact h 2 (by omega) (by decide)

/-- `4^7 = 16384 = 211110211₃` fires at row eight: seven is not a
shadow. -/
theorem not_shadow_seven : ¬ EternallyShadowed 7 := by
  intro hE
  have h := (eternally_shadowed_iff_bounded_window 7 9 (by decide)).mp hE
  exact h 8 (by omega) (by decide)

/-! ## Section 5 — the exact set below eight -/

/-- **THE EXACT SET BELOW EIGHT.**  The eternally shadowed exponents
below eight are exactly `0, 1, 4` — the three paid shadows; every other
exponent in the range fires a digit two. -/
theorem shadow_below_eight :
    ∀ m : Nat, m < 8 →
      (EternallyShadowed m ↔ m = 0 ∨ m = 1 ∨ m = 4) := by
  intro m hm
  have hex : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨
      m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun _ => Or.inl rfl, fun _ => shadow_zero⟩
  · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => shadow_one⟩
  · exact ⟨fun hE => absurd hE not_shadow_two,
      fun h => absurd h (by decide)⟩
  · exact ⟨fun hE => absurd hE not_shadow_three,
      fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => shadow_four⟩
  · exact ⟨fun hE => absurd hE not_shadow_five,
      fun h => absurd h (by decide)⟩
  · exact ⟨fun hE => absurd hE not_shadow_six,
      fun h => absurd h (by decide)⟩
  · exact ⟨fun hE => absurd hE not_shadow_seven,
      fun h => absurd h (by decide)⟩

/-! ## Section 6 — the sharpened battle -/

/-- **DOOR FOURTEEN — the exhibited shadow set.**  If the eternally
shadowed exponents are among `0, 1, 4` — the three shadows this module
pays — the full unconditional theorem follows. -/
theorem crown_of_shadow_set
    (h : ∀ m : Nat, EternallyShadowed m → m = 0 ∨ m = 1 ∨ m = 4) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  THE_REMAINING_CONTENT.mpr
    (fun m hm hE => by rcases h m hE with h0 | h1 | h4 <;> omega)

/-- **THE SHARPENED BATTLE.**  The comparator's unconditional statement
is equivalent to the shadow set being exactly the three exhibited
shadows.  Both memberships (`0, 1, 4` are shadows) and the finite base
(no other exponent below eight) are paid in this module; the remaining
content of the entire war is the upper bound alone: no shadow from five
upward.  This is the strongest named form the campaign has ever reduced
itself to. -/
theorem shadow_set_iff_exhibited :
    (∀ m : Nat, EternallyShadowed m ↔ m = 0 ∨ m = 1 ∨ m = 4) ↔
      (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) := by
  constructor
  · intro h
    exact crown_of_shadow_set (fun m hE => (h m).mp hE)
  · intro hcrown m
    constructor
    · intro hE
      rcases Nat.lt_or_ge m 5 with h5 | h5
      · exact (shadow_below_eight m (by omega)).mp hE
      · exact absurd hE (THE_REMAINING_CONTENT.mp hcrown m h5)
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact shadow_zero
      · exact shadow_one
      · exact shadow_four

/-- **THE ONE BATTLE, SHARPENED AND BASED.**  The comparator statement
is the statement that the shadow set is exactly the three exhibited
shadows — and the three exhibited shadows are paid. -/
theorem the_one_battle_exhibited :
    ((∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ↔
      (∀ m : Nat, EternallyShadowed m ↔ m = 0 ∨ m = 1 ∨ m = 4)) ∧
    (EternallyShadowed 0 ∧ EternallyShadowed 1 ∧ EternallyShadowed 4) :=
  ⟨shadow_set_iff_exhibited.symm, shadow_zero, shadow_one, shadow_four⟩

/-! ## Section 7 — the element law -/

/-- **THE ELEMENT LAW.**  Every eternal shadow sits in a surviving
class at every level: its residue mod `3^L` is on the exhibited
survivor list of the shadow gap, at all scales. -/
theorem shadow_class_all_levels (m L : Nat) (hE : EternallyShadowed m) :
    m % 3^L ∈ GSTShadowSeparationAttack.survivorClasses L := by
  have h3L : 0 < 3^L := by positivity
  refine GSTShadowSeparationAttack.survivorClasses_complete L (m % 3^L)
    (Nat.mod_lt _ h3L) ?_
  intro p hp
  have hcls : 4^m % 3^(L+1) = 4^(m % 3^L) % 3^(L+1) :=
    pow4_mod_window_class L m
  have h1 : digit3 (4^m % 3^(L+1)) p = digit3 (4^m) p :=
    digit3_mod_window (4^m) (L+1) p hp
  have h2 : digit3 (4^(m % 3^L) % 3^(L+1)) p = digit3 (4^(m % 3^L)) p :=
    digit3_mod_window _ (L+1) p hp
  rw [← h2, ← hcls, h1]
  exact hE L p hp

/-- **THE SHADOW IS A LIST ELEMENT.**  Above its own size, an eternal
shadow is itself an element of the exhibited survivor list: the shadow
`m` lies on the level-`L` survivor list for every `3^L > m`.  Any
counterexample to the conjecture is an element of the doubling shadow
at every scale beyond its own magnitude. -/
theorem shadow_is_element (m L : Nat) (hE : EternallyShadowed m)
    (hL : m < 3^L) :
    m ∈ GSTShadowSeparationAttack.survivorClasses L := by
  have hmem := shadow_class_all_levels m L hE
  rw [Nat.mod_eq_of_lt hL] at hmem
  exact hmem

/-- **THE LEVEL-SEVEN CLASS CONSTRAINT.**  Any eternal shadow from five
on lies in one of the `128` surviving classes of the level-seven table:
its class mod `2187` is on `survivorTable7`.  A counterexample to the
Erdős ternary conjecture is pinned, unconditionally, to one of these
`128` residue classes. -/
theorem shadow_survivor_seven (m : Nat) (_hm : 5 ≤ m)
    (hE : EternallyShadowed m) :
    survivor7 (m % 2187) = true := by
  rcases level_seven_reach m with h | ⟨p, hp8, hp⟩
  · exact h
  · exact absurd hp (hE 7 p (by omega))

/-! ## Section 8 — receipts -/

#print axioms eternally_shadowed_iff_bounded_window
#print axioms eternally_shadowed_iff_cantorian
#print axioms shadow_zero
#print axioms shadow_one
#print axioms shadow_four
#print axioms not_shadow_two
#print axioms not_shadow_three
#print axioms not_shadow_five
#print axioms not_shadow_six
#print axioms not_shadow_seven
#print axioms shadow_below_eight
#print axioms crown_of_shadow_set
#print axioms shadow_set_iff_exhibited
#print axioms the_one_battle_exhibited
#print axioms shadow_class_all_levels
#print axioms shadow_is_element
#print axioms shadow_survivor_seven

end GSTShadowExhibited
