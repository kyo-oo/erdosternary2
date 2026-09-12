import GSTFourPowerAffineSuccessEquivalence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineTerminalCollision

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineIteratedRelocation

/-- In channel state `0`, source trit `2` is an immediate exact low success. -/
theorem lowSuccess_of_state_zero_digit_two
    (x : Nat) (hx : lowDigit x = 2) :
    lowSuccess 0 x := by
  constructor
  · exact hx
  · simp [channelOut, hx]

/-- In channel state `3`, source trit `2` is likewise an immediate exact low success. -/
theorem lowSuccess_of_state_three_digit_two
    (x : Nat) (hx : lowDigit x = 2) :
    lowSuccess 3 x := by
  constructor
  · exact hx
  · simp [channelOut, hx]

/-- A finite affine-channel collision with terminal-success state `0` or `3`
and current source trit `2` constructs a direct common-two witness at that
same affine row `n`. -/
theorem terminal_collision_constructs_commonTwo
    (N n : Nat)
    (hstate :
      iterChannel n 1 (affineOrbit N) = 0 ∨
      iterChannel n 1 (affineOrbit N) = 3)
    (hdigit : lowDigit (iterSource n (affineOrbit N)) = 2) :
    CommonTwo N := by
  have hs :
      lowSuccess
        (iterChannel n 1 (affineOrbit N))
        (iterSource n (affineOrbit N)) := by
    rcases hstate with h0 | h3
    · rw [h0]
      exact lowSuccess_of_state_zero_digit_two _ hdigit
    · rw [h3]
      exact lowSuccess_of_state_three_digit_two _ hdigit
  exact iterated_affine_low_success_constructs_commonTwo N n hs

/-- Physical Task-3 endpoint.  The terminal state/source-trit collision does
not merely prove existence: it constructs the actual relocated Happy row
`q = n+1`, hence `q ≥ 1`, on the next four-power exponent. -/
theorem terminal_collision_constructs_exact_relocated_row
    (K n : Nat)
    (hstate :
      iterChannel n 1 (affineOrbit (K+1)) = 0 ∨
      iterChannel n 1 (affineOrbit (K+1)) = 3)
    (hdigit : lowDigit (iterSource n (affineOrbit (K+1))) = 2) :
    ∃ q : Nat, q = n+1 ∧ 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have hs :
      lowSuccess
        (iterChannel n 1 (affineOrbit (K+1)))
        (iterSource n (affineOrbit (K+1))) := by
    rcases hstate with h0 | h3
    · rw [h0]
      exact lowSuccess_of_state_zero_digit_two _ hdigit
    · rw [h3]
      exact lowSuccess_of_state_three_digit_two _ hdigit
  exact iterated_affine_low_success_constructs_exact_relocated_row K n hs

/-- Exact obstruction exposed by a hypothetical direct counterexample: at no
finite depth may the live channel be `0` or `3` while the live source trit is
`2`.  Otherwise the theorem above constructs `CommonTwo N` immediately. -/
theorem noCommonTwo_forces_terminal_collision_avoidance
    (N n : Nat) (hNo : ¬ CommonTwo N) :
    ¬ ((iterChannel n 1 (affineOrbit N) = 0 ∨
        iterChannel n 1 (affineOrbit N) = 3) ∧
       lowDigit (iterSource n (affineOrbit N)) = 2) := by
  intro h
  exact hNo (terminal_collision_constructs_commonTwo N n h.1 h.2)

#check lowSuccess_of_state_zero_digit_two
#check lowSuccess_of_state_three_digit_two
#check terminal_collision_constructs_commonTwo
#check terminal_collision_constructs_exact_relocated_row
#check noCommonTwo_forces_terminal_collision_avoidance
#print axioms lowSuccess_of_state_zero_digit_two
#print axioms lowSuccess_of_state_three_digit_two
#print axioms terminal_collision_constructs_commonTwo
#print axioms terminal_collision_constructs_exact_relocated_row
#print axioms noCommonTwo_forces_terminal_collision_avoidance

end GSTFourPowerAffineTerminalCollision
