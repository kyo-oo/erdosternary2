import GSTFourPowerExactRowRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineIteratedRelocation

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerDirectHappyBridge
open GSTFourPowerExactRowRelocation
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge

/-- Source remaining after exactly `n` ternary channel reads. -/
def iterSource : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => iterSource n (tail3 x)

/-- Channel state remaining after exactly `n` ternary reads.  The source and
channel are advanced together by the exact finite-state arithmetic recurrence. -/
def iterChannel : Nat → Nat → Nat → Nat
  | 0, c, _ => c
  | n+1, c, x =>
      iterChannel n (channelNext c (lowDigit x)) (tail3 x)

/-- A low success reached after any finite number of exact affine-channel
steps lifts back to a common digit two at the same original row `n`.
This is an arithmetic digit lift only: no graph navigation or witness
transport is involved. -/
theorem iterated_lowSuccess_pair_at_exact_row
    (c x n : Nat)
    (h : lowSuccess (iterChannel n c x) (iterSource n x)) :
    digit3 x n = 2 ∧ digit3 (4*x+c) n = 2 := by
  induction n generalizing c x with
  | zero =>
      constructor
      · rw [digit3_zero_source]
        exact h.1
      · rw [digit3_zero_channel]
        exact h.2
  | succ n ih =>
      have ht := ih
        (c := channelNext c (lowDigit x))
        (x := tail3 x)
        (by simpa [iterSource, iterChannel] using h)
      constructor
      · rw [digit3_succ_tail x n]
        exact ht.1
      · rw [digit3_succ_channel c x n]
        exact ht.2

/-- Witness form of the arbitrary-depth channel lift. -/
theorem iterated_lowSuccess_constructs_pair_common_two
    (c x n : Nat)
    (h : lowSuccess (iterChannel n c x) (iterSource n x)) :
    PairCommonTwo x (4*x+c) := by
  have hr := iterated_lowSuccess_pair_at_exact_row c x n h
  exact ⟨n, hr.1, hr.2⟩

/-- Row-preserving four-power form of the arbitrary-depth channel lift.
A success after `n` affine reads is not merely existential: after restoring the
consumed low four-power trit, the physical relocated row is exactly `n+1`. -/
theorem iterated_affine_low_success_forces_happy_at_exact_row
    (K n : Nat)
    (h : lowSuccess
      (iterChannel n 1 (affineOrbit (K+1)))
      (iterSource n (affineOrbit (K+1)))) :
    GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) (n+1))
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) (n+1)) := by
  have hr := iterated_lowSuccess_pair_at_exact_row
    1 (affineOrbit (K+1)) n h
  have hs : digit3 (4^(K+1)) (n+1) = 2 := by
    rw [four_pow_digit_affine_shift (K+1) n]
    exact hr.1
  have ht : digit3 (4^((K+1)+1)) (n+1) = 2 := by
    rw [four_pow_digit_affine_shift ((K+1)+1) n]
    rw [affineOrbit_forward (K+1)]
    exact hr.2
  exact commonTwo_exact_row_to_physical_happy (K+1) (n+1) hs ht

/-- Fresh arbitrary-depth exact relocation constructor.  Starting from the
channel-one affine representation of the next four-power exponent, any finite
channel depth at which the low pair succeeds returns the concrete physical
Happy witness `q = n+1 ≥ 1` on `4^(K+1)`.

Unlike the fixed row-2/3/4 classifiers or bounded-prefix sectors, `n` is
unbounded.  The remaining universal pressure point is to force such a finite
low-success depth for every admissible next exponent. -/
theorem iterated_affine_low_success_constructs_exact_relocated_row
    (K n : Nat)
    (h : lowSuccess
      (iterChannel n 1 (affineOrbit (K+1)))
      (iterSource n (affineOrbit (K+1)))) :
    ∃ q : Nat, q = n+1 ∧ 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  refine ⟨n+1, rfl, by omega, ?_⟩
  exact iterated_affine_low_success_forces_happy_at_exact_row K n h

/-- Task-3-shaped existential adapter retained for direct use by the current
forcing interface.  Its witness is the exact row `n+1` constructed above. -/
theorem iterated_affine_low_success_constructs_relocated_physical_happy
    (K n : Nat)
    (h : lowSuccess
      (iterChannel n 1 (affineOrbit (K+1)))
      (iterSource n (affineOrbit (K+1)))) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rcases iterated_affine_low_success_constructs_exact_relocated_row K n h with
    ⟨q, _, hq, hHappy⟩
  exact ⟨q, hq, hHappy⟩

#check iterSource
#check iterChannel
#check iterated_lowSuccess_pair_at_exact_row
#check iterated_lowSuccess_constructs_pair_common_two
#check iterated_affine_low_success_forces_happy_at_exact_row
#check iterated_affine_low_success_constructs_exact_relocated_row
#check iterated_affine_low_success_constructs_relocated_physical_happy
#print axioms iterated_lowSuccess_pair_at_exact_row
#print axioms iterated_lowSuccess_constructs_pair_common_two
#print axioms iterated_affine_low_success_forces_happy_at_exact_row
#print axioms iterated_affine_low_success_constructs_exact_relocated_row
#print axioms iterated_affine_low_success_constructs_relocated_physical_happy

end GSTFourPowerAffineIteratedRelocation
