import GSTFourPowerAffineBadState

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineChannelAutomaton

open GSTFourPowerDirectResidue
open GSTFourPowerAffineBadState

/-- Least ternary digit of a channel source. -/
def lowDigit (x : Nat) : Nat := x % 3

/-- One-digit ternary tail. -/
def tail3 (x : Nat) : Nat := x / 3

/-- Low output digit of the affine channel `x ↦ 4x+c`. -/
def channelOut (c a : Nat) : Nat := (4*a + c) % 3

/-- Carry/channel state passed to the next ternary digit. -/
def channelNext (c a : Nat) : Nat := (4*a + c) / 3

/-- The low pair is already a common two. -/
def lowSuccess (c x : Nat) : Prop :=
  lowDigit x = 2 ∧ channelOut c (lowDigit x) = 2

/-- Global badness of one affine channel. -/
def BadChannel (c x : Nat) : Prop :=
  ¬ PairCommonTwo x (4*x + c)

lemma lowDigit_lt_three (x : Nat) : lowDigit x < 3 := by
  exact Nat.mod_lt _ (by decide)

/-- Exact one-trit decomposition. -/
theorem split_three (x : Nat) :
    x = lowDigit x + 3 * tail3 x := by
  simpa [lowDigit, tail3] using (Nat.mod_add_div x 3).symm

/-- Exact one-trit decomposition of the affine target. -/
theorem split_channel (c x : Nat) :
    4*x + c =
      channelOut c (lowDigit x) +
        3 * (4 * tail3 x + channelNext c (lowDigit x)) := by
  rw [split_three x]
  unfold channelOut channelNext
  have hz := (Nat.mod_add_div (4 * lowDigit x + c) 3).symm
  omega

/-- Removing one ternary digit from the source shifts every higher digit
    literally onto the quotient. -/
theorem digit3_succ_tail (x j : Nat) :
    digit3 x (j+1) = digit3 (tail3 x) j := by
  rw [split_three x]
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 (lowDigit x) (tail3 x) j (by simpa using lowDigit_lt_three x)
  simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Removing one ternary digit from `4x+c` exposes the next finite channel. -/
theorem digit3_succ_channel (c x j : Nat) :
    digit3 (4*x+c) (j+1) =
      digit3 (4 * tail3 x + channelNext c (lowDigit x)) j := by
  rw [split_channel c x]
  have hout : channelOut c (lowDigit x) < 3 := by
    unfold channelOut
    exact Nat.mod_lt _ (by decide)
  have h := GSTCanonicalTailStateIso.prefix_slice_digit_exact
    1 (channelOut c (lowDigit x))
      (4 * tail3 x + channelNext c (lowDigit x)) j
      (by simpa using hout)
  simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

@[simp] theorem digit3_zero_source (x : Nat) :
    digit3 x 0 = lowDigit x := by
  simp [GSTFourPowerDirectResidue.digit3, lowDigit]

@[simp] theorem digit3_zero_channel (c x : Nat) :
    digit3 (4*x+c) 0 = channelOut c (lowDigit x) := by
  rw [split_channel c x]
  have hout : channelOut c (lowDigit x) < 3 := by
    unfold channelOut
    exact Nat.mod_lt _ (by decide)
  simp [GSTFourPowerDirectResidue.digit3, Nat.mod_eq_of_lt hout]

/-- Master affine-channel recursion. Every common-two witness is either the
    discarded low digit itself, or a witness in the unique next channel. -/
theorem pairCommonTwo_channel_iff (c x : Nat) :
    PairCommonTwo x (4*x+c) ↔
      lowSuccess c x ∨
        PairCommonTwo (tail3 x)
          (4 * tail3 x + channelNext c (lowDigit x)) := by
  constructor
  · rintro ⟨j, hx, hy⟩
    cases j with
    | zero =>
        left
        constructor
        · simpa using hx
        · simpa using hy
    | succ j =>
        right
        refine ⟨j, ?_, ?_⟩
        · simpa [digit3_succ_tail] using hx
        · simpa [digit3_succ_channel] using hy
  · intro h
    rcases h with hlow | htail
    · rcases hlow with ⟨hx, hy⟩
      refine ⟨0, ?_, ?_⟩ <;> simpa using ‹_›
    · rcases htail with ⟨j, hx, hy⟩
      refine ⟨j+1, ?_, ?_⟩
      · simpa [digit3_succ_tail] using hx
      · simpa [digit3_succ_channel] using hy

/-- Complement form of the master recursion. -/
theorem badChannel_iff (c x : Nat) :
    BadChannel c x ↔
      ¬ lowSuccess c x ∧
        BadChannel (channelNext c (lowDigit x)) (tail3 x) := by
  unfold BadChannel
  rw [pairCommonTwo_channel_iff]
  simp

/-- State `0`: trit `2` is an immediate success; only `0,1` survive. -/
theorem badChannel_zero_iff (x : Nat) :
    BadChannel 0 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 1 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

/-- State `1`: all three trits survive, moving to states `0,1,3`. -/
theorem badChannel_one_iff (x : Nat) :
    BadChannel 1 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 1 (tail3 x)) ∨
      (lowDigit x = 2 ∧ BadChannel 3 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

/-- State `2`: all three trits survive, moving to states `0,2,3`. -/
theorem badChannel_two_iff (x : Nat) :
    BadChannel 2 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 2 (tail3 x)) ∨
      (lowDigit x = 2 ∧ BadChannel 3 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

/-- State `3`: trit `2` is an immediate success; only `0,1` survive. -/
theorem badChannel_three_iff (x : Nat) :
    BadChannel 3 x ↔
      (lowDigit x = 0 ∧ BadChannel 1 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 2 (tail3 x)) := by
  have ha := lowDigit_lt_three x
  rw [badChannel_iff]
  interval_cases h : lowDigit x <;>
    simp [h, lowSuccess, channelOut, channelNext, BadChannel] at *

#check pairCommonTwo_channel_iff
#check badChannel_iff
#check badChannel_zero_iff
#check badChannel_one_iff
#check badChannel_two_iff
#check badChannel_three_iff
#print axioms pairCommonTwo_channel_iff
#print axioms badChannel_zero_iff
#print axioms badChannel_one_iff
#print axioms badChannel_two_iff
#print axioms badChannel_three_iff

end GSTFourPowerAffineChannelAutomaton
