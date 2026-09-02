import GSTFourPowerDirectExistence
import GSTFourPowerDirectNo22

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectFailedRelocationState

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry
open GSTFourPowerDirectNo22

/-- A failed relocation has a rigid physical arithmetic state immediately
above every source common-two witness.  If row `p` is common for `4^K` and
`4^(K+1)`, but the next sheet has no common-two row anywhere, then on the
`4^(K+1)` source for the next x4 step:

* the binary carry entering row `p+1` is exactly one;
* hence the physical multiplication carry there is exactly three; and
* the source digit at row `p+1` is not two.

This is the direct-arithmetic replacement for the old latent navigation
packet.  It uses the actual witness row and no witness transport. -/
theorem failed_relocation_forces_post_witness_state
    (K p : Nat) (hp : 1 ≤ p)
    (hSource : digit3 (4^K) p = 2)
    (hTarget : digit3 (4^(K+1)) p = 2)
    (hNoNext : ¬ CommonTwo (K+1)) :
    binaryCarry (4^(K+1)) (p+1) = 1 ∧
      directCarry4 (4^(K+1)) (p+1) = 3 ∧
      digit3 (4^(K+1)) (p+1) ≠ 2 := by
  have hNoMul : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^(K+1)) q = 2 ∧
      digit3 (4 * (4^(K+1))) q = 2 := by
    intro h
    rcases h with ⟨q, hq, hs, ht⟩
    apply hNoNext
    refine ⟨q, hq, hs, ?_⟩
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
  have hbit : binaryCarry (4^(K+1)) (p+1) = 1 :=
    source_two_forces_next_binary_one_of_no_common
      (4^(K+1)) p hp hNoMul hTarget
  have hcarryEq :=
    directCarry4_eq_prev_digit_add_binary (4^(K+1)) (p+1) (by omega)
  have hprev : digit3 (4^(K+1)) ((p+1)-1) = 2 := by
    simpa using hTarget
  rw [hprev, hbit] at hcarryEq
  have hcarry : directCarry4 (4^(K+1)) (p+1) = 3 := by
    omega
  have hnot2 : digit3 (4^(K+1)) (p+1) ≠ 2 :=
    no_common_forbids_source_22 (4^(K+1)) p hp hNoMul hTarget
  exact ⟨hbit, hcarry, hnot2⟩

/-- Bundled existential form starting from the actual source `CommonTwo`
witness.  Any hypothetical failure of relocation therefore produces a real
row `p ≥ 1` whose next physical carry is exactly three. -/
theorem commonTwo_failed_relocation_has_carry_three_row
    (K : Nat) (hCommon : CommonTwo K) (hNoNext : ¬ CommonTwo (K+1)) :
    ∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧
      digit3 (4^(K+1)) p = 2 ∧
      directCarry4 (4^(K+1)) (p+1) = 3 ∧
      digit3 (4^(K+1)) (p+1) ≠ 2 := by
  rcases hCommon with ⟨p, hp, hs, ht⟩
  have hstate :=
    failed_relocation_forces_post_witness_state K p hp hs ht hNoNext
  exact ⟨p, hp, hs, ht, hstate.2.1, hstate.2.2⟩

#check failed_relocation_forces_post_witness_state
#check commonTwo_failed_relocation_has_carry_three_row
#print axioms failed_relocation_forces_post_witness_state
#print axioms commonTwo_failed_relocation_has_carry_three_row

end GSTFourPowerDirectFailedRelocationState
