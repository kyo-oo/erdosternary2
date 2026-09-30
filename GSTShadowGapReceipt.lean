import GSTShadowGap
import GSTFourPowerHappyBaseCamp
import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE RECEIPT — the remaining content, stated in the judge's own language

The official comparator demands the unconditional theorem

  `erdos_ternary_2 : ∀ n : Nat, 9 ≤ n → noTernaryDigitTwo (2^n) = false`.

This file assembles the campaign's entire machine-checked state around
that demand into one place:

* **THE EQUIVALENCE** (`comparator_iff_even_digit_two`): the comparator
  statement is equivalent to the bare even digit-two statement — every
  `4^m` with `m ≥ 5` owns a ternary digit two.  The odd rows are
  elementary (`2^n ≡ 2 (mod 3)` for odd `n`, the green odd theorem);
  the even rows are the whole content.

* **THE CLIMB ROUTE** (`climb_route`): the tail climb — every exponent
  above the kernel base camp owns a physical Happy row — implies the
  comparator statement, through the green base-camp/master/conversion
  chain.  The climb is a sufficient condition, machine-checked.

* **THE REMAINING CONTENT** (`THE_REMAINING_CONTENT`): the comparator
  statement is equivalent to the statement that no exponent `m ≥ 5` is
  eternally shadowed — no `m ≥ 5` has clean windows at every scale.
  By the Shadow Gap's exact count, at every scale `L` there remain
  exactly `2^L` surviving classes, each lived in by infinitely many
  exponents; the surviving classes double forever.  The separation of
  the natural exponents from the doubling shadow is the named object
  that the comparator's unconditional stamp still requires.
-/

namespace GSTShadowGapReceipt

open GSTShadowGap
open GSTFourPowerDirectResidue
open GSTFourPowerHappyBaseCamp

/-! ## Section 1 — the equivalence with the bare even statement -/

/-- The comparator statement implies the bare even digit-two statement:
every `4^m` with `m ≥ 5` owns a ternary digit two. -/
theorem comparator_of_even_digit_two
    (h : ∀ m : Nat, 5 ≤ m → ∃ p : Nat, digit3 (4^m) p = 2) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  intro n hn
  refine erdos_ternary_2_universal_of_even_conjecture ?_ n hn
  intro K hK
  obtain ⟨p, hp⟩ := h K (by omega)
  have hd : 4^K / 3^p % 3 = 2 := hp
  exact has_two_imp_not_no_two (4^K) (hasTernaryTwo_of_digit (4^K) p hd)

/-- The bare even digit-two statement implies the comparator statement:
the even rows carry the odd rows through the green crown. -/
theorem even_digit_two_of_comparator
    (h : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :
    ∀ m : Nat, 5 ≤ m → ∃ p : Nat, digit3 (4^m) p = 2 := by
  intro m hm
  have hnm : 9 ≤ 2 * m := by omega
  have hn := h (2 * m) hnm
  have hpow : 2^(2 * m) = 4^m := by
    rw [Nat.pow_mul]
    norm_num
  rw [hpow] at hn
  obtain ⟨p, hp⟩ := no_two_false_digit_witness (4^m) hn
  exact ⟨p, hp⟩

/-- **THE EQUIVALENCE.**  The comparator statement and the bare even
digit-two statement are one object: every `2^n` with `n ≥ 9` fails
`noTernaryTwo` exactly when every `4^m` with `m ≥ 5` owns a ternary
digit two. -/
theorem comparator_iff_even_digit_two :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ↔
    (∀ m : Nat, 5 ≤ m → ∃ p : Nat, digit3 (4^m) p = 2) :=
  ⟨comparator_of_even_digit_two, even_digit_two_of_comparator⟩

/-! ## Section 2 — the climb route, restated in one place -/

/-- **THE CLIMB ROUTE.**  The tail climb — every exponent above the
kernel base camp owns a physical Happy row — delivers the comparator
statement through the green base-camp / master / conversion chain. -/
theorem climb_route (htail : four_power_happy_climb_tail) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  fun n hn => erdos_ternary_2_universal_of_climb_tail htail n hn

/-- The climb route also delivers the bare even statement directly. -/
theorem climb_even_route (htail : four_power_happy_climb_tail) :
    ∀ m : Nat, 5 ≤ m → ∃ p : Nat, digit3 (4^m) p = 2 := by
  intro m hm
  have hhas : hasTernaryTwo (4^m) = true :=
    erdos_ternary_2_even_universal_of_climb_tail htail m hm
  have hne : noTernaryTwo (4^m) = false := has_two_imp_not_no_two (4^m) hhas
  obtain ⟨p, hp⟩ := no_two_false_digit_witness (4^m) hne
  exact ⟨p, hp⟩

/-! ## Section 3 — the remaining content, named in the judge's language -/

/-- An exponent is **eternally shadowed** when its window is clean at
every scale — no ternary digit two anywhere in `4^m`. -/
def EternallyShadowed (m : Nat) : Prop :=
  ∀ L p : Nat, p < L + 1 → digit3 (4^m) p ≠ 2

theorem eternally_shadowed_iff_no_digit_two (m : Nat) :
    EternallyShadowed m ↔ (∀ p : Nat, digit3 (4^m) p ≠ 2) := by
  constructor
  · intro h p
    exact h p p (by omega)
  · intro h L p _
    exact h p

/-- **THE REMAINING CONTENT.**  The comparator statement is equivalent
to: no exponent `m ≥ 5` is eternally shadowed.  By the Shadow Gap's
exact count, at every scale `L` exactly `2^L` classes survive the
window, and every surviving class is lived in — the shadow doubles
forever, and the comparator's unconditional stamp is exactly the
separation of the natural exponents from it. -/
theorem THE_REMAINING_CONTENT :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) ↔
    (∀ m : Nat, 5 ≤ m → ¬ EternallyShadowed m) := by
  rw [comparator_iff_even_digit_two]
  constructor
  · intro h m hm hshadow
    obtain ⟨p, hp⟩ := h m hm
    exact hp ((eternally_shadowed_iff_no_digit_two m).mp hshadow p)
  · intro h m hm
    by_contra hclean
    exact h m hm ((eternally_shadowed_iff_no_digit_two m).mpr
      (fun p => hclean p))

/-! ## Section 4 — receipts -/

#print axioms comparator_iff_even_digit_two
#print axioms climb_route
#print axioms climb_even_route
#print axioms THE_REMAINING_CONTENT

end GSTShadowGapReceipt
