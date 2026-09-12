import GSTFourPowerAffineTerminalCollision

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineConsecutiveTwoRelocation

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineIteratedRelocation
open GSTFourPowerAffineTerminalCollision

/-- The affine carry state never leaves the exact four-state set `0,1,2,3`
once it starts there. -/
theorem channelNext_le_three_of_le_three
    (c a : Nat) (hc : c ≤ 3) (ha : a < 3) :
    channelNext c a ≤ 3 := by
  interval_cases c <;> interval_cases a <;>
    norm_num [channelNext] at *

/-- Forward recursion for the source after `n` exact ternary reads. -/
theorem iterSource_succ (n x : Nat) :
    iterSource (n+1) x = tail3 (iterSource n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simpa [iterSource] using ih (tail3 x)

/-- Forward recursion for the live affine carry state.  This exposes the state
at depth `n+1` directly from the state/source pair at depth `n`. -/
theorem iterChannel_succ (n c x : Nat) :
    iterChannel (n+1) c x =
      channelNext (iterChannel n c x) (lowDigit (iterSource n x)) := by
  induction n generalizing c x with
  | zero => rfl
  | succ n ih =>
      simpa [iterChannel, iterSource] using
        ih (channelNext c (lowDigit x)) (tail3 x)

/-- Starting from channel state `1`, every finite live state is one of
`0,1,2,3`. -/
theorem iterChannel_le_three
    (n c x : Nat) (hc : c ≤ 3) :
    iterChannel n c x ≤ 3 := by
  induction n generalizing c x with
  | zero => simpa [iterChannel] using hc
  | succ n ih =>
      rw [iterChannel_succ]
      exact channelNext_le_three_of_le_three
        (iterChannel n c x) (lowDigit (iterSource n x))
        (ih c x hc) (lowDigit_lt_three _)

/-- Under a hypothetical direct counterexample, seeing source trit `2` forces
the live state to be exactly `1` or `2`: states `0` and `3` would already be
a terminal collision. -/
theorem noCommonTwo_digit_two_forces_state_one_or_two
    (N n : Nat) (hNo : ¬ CommonTwo N)
    (hdigit : lowDigit (iterSource n (affineOrbit N)) = 2) :
    iterChannel n 1 (affineOrbit N) = 1 ∨
    iterChannel n 1 (affineOrbit N) = 2 := by
  have hb : iterChannel n 1 (affineOrbit N) ≤ 3 :=
    iterChannel_le_three n 1 (affineOrbit N) (by omega)
  have h0 : iterChannel n 1 (affineOrbit N) ≠ 0 := by
    intro hs
    exact noCommonTwo_forces_terminal_collision_avoidance N n hNo
      ⟨Or.inl hs, hdigit⟩
  have h3 : iterChannel n 1 (affineOrbit N) ≠ 3 := by
    intro hs
    exact noCommonTwo_forces_terminal_collision_avoidance N n hNo
      ⟨Or.inr hs, hdigit⟩
  omega

/-- A surviving source trit `2` sends either nonterminal state `1` or `2`
exactly to terminal-success state `3` at the next row. -/
theorem noCommonTwo_digit_two_forces_next_state_three
    (N n : Nat) (hNo : ¬ CommonTwo N)
    (hdigit : lowDigit (iterSource n (affineOrbit N)) = 2) :
    iterChannel (n+1) 1 (affineOrbit N) = 3 := by
  have hs := noCommonTwo_digit_two_forces_state_one_or_two N n hNo hdigit
  rw [iterChannel_succ]
  rcases hs with h1 | h2
  · rw [h1, hdigit]
    norm_num [channelNext]
  · rw [h2, hdigit]
    norm_num [channelNext]

/-- Therefore a counterexample affine source can never contain two consecutive
live trits equal to `2`. -/
theorem noCommonTwo_forces_no_consecutive_source_twos
    (N n : Nat) (hNo : ¬ CommonTwo N)
    (hdigit : lowDigit (iterSource n (affineOrbit N)) = 2) :
    lowDigit (iterSource (n+1) (affineOrbit N)) ≠ 2 := by
  intro hnext
  have hs := noCommonTwo_digit_two_forces_next_state_three N n hNo hdigit
  exact noCommonTwo_forces_terminal_collision_avoidance N (n+1) hNo
    ⟨Or.inr hs, hnext⟩

/-- Constructive converse of the obstruction: two consecutive source trits `2`
always produce a direct `CommonTwo` witness.  If the first live state is `0/3`
the success is at depth `n`; if it is `1/2`, that trit sends the channel to
state `3`, so the second `2` succeeds at depth `n+1`. -/
theorem consecutive_source_twos_construct_commonTwo
    (N n : Nat)
    (hdigit : lowDigit (iterSource n (affineOrbit N)) = 2)
    (hnext : lowDigit (iterSource (n+1) (affineOrbit N)) = 2) :
    CommonTwo N := by
  have hb : iterChannel n 1 (affineOrbit N) ≤ 3 :=
    iterChannel_le_three n 1 (affineOrbit N) (by omega)
  have hcases :
      iterChannel n 1 (affineOrbit N) = 0 ∨
      iterChannel n 1 (affineOrbit N) = 1 ∨
      iterChannel n 1 (affineOrbit N) = 2 ∨
      iterChannel n 1 (affineOrbit N) = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact terminal_collision_constructs_commonTwo N n (Or.inl h0) hdigit
  · have hs : iterChannel (n+1) 1 (affineOrbit N) = 3 := by
      rw [iterChannel_succ, h1, hdigit]
      norm_num [channelNext]
    exact terminal_collision_constructs_commonTwo N (n+1) (Or.inr hs) hnext
  · have hs : iterChannel (n+1) 1 (affineOrbit N) = 3 := by
      rw [iterChannel_succ, h2, hdigit]
      norm_num [channelNext]
    exact terminal_collision_constructs_commonTwo N (n+1) (Or.inr hs) hnext
  · exact terminal_collision_constructs_commonTwo N n (Or.inr h3) hdigit

/-- Physical Task-3 endpoint.  Two consecutive source trits `2` construct an
actual relocated Happy row immediately: it is either `q = n+1` or `q = n+2`,
and hence always `q ≥ 1`. -/
theorem consecutive_source_twos_construct_exact_relocated_row
    (K n : Nat)
    (hdigit : lowDigit (iterSource n (affineOrbit (K+1))) = 2)
    (hnext : lowDigit (iterSource (n+1) (affineOrbit (K+1))) = 2) :
    ∃ q : Nat, (q = n+1 ∨ q = n+2) ∧ 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  have hb : iterChannel n 1 (affineOrbit (K+1)) ≤ 3 :=
    iterChannel_le_three n 1 (affineOrbit (K+1)) (by omega)
  have hcases :
      iterChannel n 1 (affineOrbit (K+1)) = 0 ∨
      iterChannel n 1 (affineOrbit (K+1)) = 1 ∨
      iterChannel n 1 (affineOrbit (K+1)) = 2 ∨
      iterChannel n 1 (affineOrbit (K+1)) = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · rcases terminal_collision_constructs_exact_relocated_row
        K n (Or.inl h0) hdigit with ⟨q, hq, hq1, hHappy⟩
    exact ⟨q, Or.inl hq, hq1, hHappy⟩
  · have hs : iterChannel (n+1) 1 (affineOrbit (K+1)) = 3 := by
      rw [iterChannel_succ, h1, hdigit]
      norm_num [channelNext]
    rcases terminal_collision_constructs_exact_relocated_row
        K (n+1) (Or.inr hs) hnext with ⟨q, hq, hq1, hHappy⟩
    refine ⟨q, Or.inr ?_, hq1, hHappy⟩
    omega
  · have hs : iterChannel (n+1) 1 (affineOrbit (K+1)) = 3 := by
      rw [iterChannel_succ, h2, hdigit]
      norm_num [channelNext]
    rcases terminal_collision_constructs_exact_relocated_row
        K (n+1) (Or.inr hs) hnext with ⟨q, hq, hq1, hHappy⟩
    refine ⟨q, Or.inr ?_, hq1, hHappy⟩
    omega
  · rcases terminal_collision_constructs_exact_relocated_row
        K n (Or.inr h3) hdigit with ⟨q, hq, hq1, hHappy⟩
    exact ⟨q, Or.inl hq, hq1, hHappy⟩

#check channelNext_le_three_of_le_three
#check iterSource_succ
#check iterChannel_succ
#check iterChannel_le_three
#check noCommonTwo_digit_two_forces_state_one_or_two
#check noCommonTwo_digit_two_forces_next_state_three
#check noCommonTwo_forces_no_consecutive_source_twos
#check consecutive_source_twos_construct_commonTwo
#check consecutive_source_twos_construct_exact_relocated_row
#print axioms channelNext_le_three_of_le_three
#print axioms iterSource_succ
#print axioms iterChannel_succ
#print axioms iterChannel_le_three
#print axioms noCommonTwo_digit_two_forces_state_one_or_two
#print axioms noCommonTwo_digit_two_forces_next_state_three
#print axioms noCommonTwo_forces_no_consecutive_source_twos
#print axioms consecutive_source_twos_construct_commonTwo
#print axioms consecutive_source_twos_construct_exact_relocated_row

end GSTFourPowerAffineConsecutiveTwoRelocation
