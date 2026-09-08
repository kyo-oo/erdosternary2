import GSTFourPowerThreeStepBadnessDescent
import GSTFourPowerAffineChannelAutomaton
import GSTFourPowerAffineOrbit
import GSTFourPowerDirectAdditionCarry
import GSTPerfectPowerTailNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerThreeStepQuotientChannel

open GSTFourPowerDirectResidue
open GSTFourPowerDirectAdditionCarry
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerThreeStepBadnessDescent
open GSTPerfectPowerTailNavigation

/-- Common digit-two strictly from affine row two upward. -/
def PairCommonTwoFromTwo (x y : Nat) : Prop :=
  ∃ q : Nat, 2 ≤ q ∧ digit3 x q = 2 ∧ digit3 y q = 2

/-- Source after deleting two low ternary digits. -/
def tail9 (x : Nat) : Nat := tail3 (tail3 x)

/-- Affine-channel state after consuming exactly two source trits. -/
def channelAfterTwo (c x : Nat) : Nat :=
  channelNext
    (channelNext c (lowDigit x))
    (lowDigit (tail3 x))

theorem tail9_eq_div_nine (x : Nat) :
    tail9 x = x / 9 := by
  simp [tail9, tail3, Nat.div_div_eq_div_mul]

/-- Exact two-trit source shift. -/
theorem digit3_add_two_tail9 (x j : Nat) :
    digit3 x (j+2) = digit3 (tail9 x) j := by
  have h0 := digit3_succ_tail x (j+1)
  have h1 := digit3_succ_tail (tail3 x) j
  dsimp [tail9]
  rw [show j + 2 = (j+1)+1 by omega, h0]
  simpa using h1

/-- Exact two-trit target shift for an arbitrary affine channel. -/
theorem digit3_add_two_channel
    (c x j : Nat) :
    digit3 (4*x+c) (j+2) =
      digit3 (4 * tail9 x + channelAfterTwo c x) j := by
  have h0 := digit3_succ_channel c x (j+1)
  have h1 := digit3_succ_channel
    (channelNext c (lowDigit x)) (tail3 x) j
  rw [show j+2 = (j+1)+1 by omega, h0]
  simpa [tail9, channelAfterTwo] using h1

/-- Deleting the first two affine trits converts the entire high common-two
problem into one ordinary finite-channel common-two problem. -/
theorem pairCommonTwoFromTwo_iff_channel
    (c x : Nat) :
    PairCommonTwoFromTwo x (4*x+c) ↔
      PairCommonTwo (tail9 x) (4 * tail9 x + channelAfterTwo c x) := by
  constructor
  · rintro ⟨q, hq, hx, hy⟩
    let j := q - 2
    have hqj : q = j+2 := by
      dsimp [j]
      omega
    refine ⟨j, ?_, ?_⟩
    · rw [← digit3_add_two_tail9 x j, ← hqj]
      exact hx
    · rw [← digit3_add_two_channel c x j, ← hqj]
      exact hy
  · rintro ⟨j, hx, hy⟩
    refine ⟨j+2, by omega, ?_, ?_⟩
    · rw [digit3_add_two_tail9 x j]
      exact hx
    · rw [digit3_add_two_channel c x j]
      exact hy

/-- Complement form: high badness is literally one BadChannel on x/9. -/
theorem noPairCommonTwoFromTwo_iff_badChannel
    (c x : Nat) :
    (¬ PairCommonTwoFromTwo x (4*x+c)) ↔
      BadChannel (channelAfterTwo c x) (tail9 x) := by
  unfold BadChannel
  exact not_congr (pairCommonTwoFromTwo_iff_channel c x)

/-- A physical Happy cell is exactly a common-two row for R and 4R. -/
theorem happyCell_iff_four_mul_common_two
    (R p : Nat) :
    GSTU2DEventTransport.HappyCell
        (GSTCanonicalSevenAxisBridge.carry4 R p)
        (GSTCanonicalSevenAxisBridge.digit3 R p) ↔
      digit3 R p = 2 ∧ digit3 (4*R) p = 2 := by
  have hcarryLt := directCarry4_lt_four R p
  have hformula := digit3_four_mul R p
  change
    GSTFourPowerDirectResidue.digit3 R p = 2 ∧
      (directCarry4 R p = 0 ∨ directCarry4 R p = 3) ↔
    GSTFourPowerDirectResidue.digit3 R p = 2 ∧
      GSTFourPowerDirectResidue.digit3 (4*R) p = 2
  constructor
  · rintro ⟨hd, h0 | h3⟩
    · refine ⟨hd, ?_⟩
      rw [hformula, hd, h0]
      decide
    · refine ⟨hd, ?_⟩
      rw [hformula, hd, h3]
      decide
  · rintro ⟨hd, ht⟩
    refine ⟨hd, ?_⟩
    rw [hformula, hd] at ht
    omega

/-- Production badness is exactly absence of affine common-two from affine
row two onward. -/
theorem badAboveThree_iff_no_affine_from_two (K : Nat) :
    BadAboveThree K ↔
      ¬ PairCommonTwoFromTwo (affineOrbit K) (affineOrbit (K+1)) := by
  constructor
  · intro hBad hPair
    rcases hPair with ⟨q, hq, h0, h1⟩
    have hp0 : digit3 (4^K) (q+1) = 2 := by
      rw [four_pow_digit_affine_shift K q]
      exact h0
    have hp1 : digit3 (4^(K+1)) (q+1) = 2 := by
      rw [four_pow_digit_affine_shift (K+1) q]
      exact h1
    have hMul : digit3 (4*(4^K)) (q+1) = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hp1
    have hHappy :=
      (happyCell_iff_four_mul_common_two (4^K) (q+1)).2 ⟨hp0, hMul⟩
    exact hBad (q+1) (by omega) hHappy
  · intro hNo p hp hHappy
    apply hNo
    have hCommon :=
      (happyCell_iff_four_mul_common_two (4^K) p).1 hHappy
    let q := p - 1
    have hpq : p = q+1 := by
      dsimp [q]
      omega
    refine ⟨q, by omega, ?_, ?_⟩
    · rw [← four_pow_digit_affine_shift K q, ← hpq]
      exact hCommon.1
    · have ht : digit3 (4^(K+1)) p = 2 := by
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          hCommon.2
      rw [← four_pow_digit_affine_shift (K+1) q, ← hpq]
      exact ht

/-- Boxed reduction: every all-depth production counterexample is one exact
four-state bad channel on the base-nine affine quotient. -/
theorem badAboveThree_iff_quotient_badChannel (K : Nat) :
    BadAboveThree K ↔
      BadChannel
        (channelAfterTwo 1 (affineOrbit K))
        (tail9 (affineOrbit K)) := by
  rw [badAboveThree_iff_no_affine_from_two]
  rw [affineOrbit_forward]
  exact noPairCommonTwoFromTwo_iff_badChannel 1 (affineOrbit K)

/-- Affine orbit composition law. -/
theorem affineOrbit_add (a b : Nat) :
    affineOrbit (a+b) = affineOrbit b + 4^b * affineOrbit a := by
  induction b with
  | zero =>
      simp [affineOrbit]
  | succ b ih =>
      rw [show a + (b+1) = (a+b)+1 by omega, affineOrbit_succ, ih,
        affineOrbit_succ, Nat.pow_succ]
      ring

/-- The nine-step affine orbit is exactly nine times the canonical level-two
perfect-power tail. -/
theorem affineOrbit_nine_mul_eq_canonicalTail_two (m : Nat) :
    affineOrbit (9*m) = 9 * canonicalTail 2 m := by
  have hAffine := four_pow_eq_one_plus_three_affineOrbit (9*m)
  have hTail := canonical_tail_decomposition 2 m
  norm_num at hTail
  nlinarith [hAffine, hTail]

/-- Original base-nine canonical quotient identity.  For K=9m+s, deleting two
affine trits exposes a fixed residue-class offset plus a scaled canonical
perfect-power tail at the strictly smaller origin m. -/
theorem affine_tail9_nine_mul_add
    (m s : Nat) :
    tail9 (affineOrbit (9*m+s)) =
      affineOrbit s / 9 + 4^s * canonicalTail 2 m := by
  rw [tail9_eq_div_nine, affineOrbit_add (9*m) s,
    affineOrbit_nine_mul_eq_canonicalTail_two]
  have h9 : 0 < (9:Nat) := by decide
  have hshape :
      affineOrbit s + 4^s * (9 * canonicalTail 2 m) =
        affineOrbit s + 9 * (4^s * canonicalTail 2 m) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ h9]

/-- Three exponent steps are the exact affine map A -> 64 A + 21. -/
theorem affineOrbit_add_three (K : Nat) :
    affineOrbit (K+3) = 64 * affineOrbit K + 21 := by
  rw [show K+3 = ((K+1)+1)+1 by omega]
  simp only [affineOrbit_succ]
  ring

#check PairCommonTwoFromTwo
#check channelAfterTwo
#check pairCommonTwoFromTwo_iff_channel
#check happyCell_iff_four_mul_common_two
#check badAboveThree_iff_no_affine_from_two
#check badAboveThree_iff_quotient_badChannel
#check affineOrbit_add
#check affineOrbit_nine_mul_eq_canonicalTail_two
#check affine_tail9_nine_mul_add
#check affineOrbit_add_three
#print axioms pairCommonTwoFromTwo_iff_channel
#print axioms happyCell_iff_four_mul_common_two
#print axioms badAboveThree_iff_quotient_badChannel
#print axioms affine_tail9_nine_mul_add

end GSTFourPowerThreeStepQuotientChannel
