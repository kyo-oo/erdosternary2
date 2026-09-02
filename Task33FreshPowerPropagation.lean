import GSTGraphV2FourPowerRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33FreshPowerPropagation

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2FourPowerRelocation

/-- Fresh Task 3.3 starting lemma.

This theorem uses only the current production relocation laws.  It does not
import any historical classifier, residual/Omega bridge, origin-descent file,
or previous candidate propagation theorem.

If a source Happy row exists on the `K` sheet but the `(K+1)` sheet has no
Happy row anywhere above row zero, then the source overlap forces an exact
latent seed on the next sheet: the same row still has information digit `2`,
the physical carry there is strictly middle (`1` or `2`), and therefore the
very next vertical carry is exactly `3`.
-/
theorem fresh_failed_edge_forces_latent_seed
    (K p : Nat)
    (hp : 1 ≤ p)
    (hSource :
      HappyCell
        (graph 1 K p).seven.carry
        (graph 1 K p).seven.digit)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    (graph 1 (K+1) p).seven.digit = 2 ∧
      ((graph 1 (K+1) p).seven.carry = 1 ∨
       (graph 1 (K+1) p).seven.carry = 2) ∧
      (graph 1 (K+1) (p+1)).seven.carry = 3 := by
  have hOverlap :=
    (graph_happy_iff_consecutive_digit_two 1 K p).mp hSource
  have hdNext : (graph 1 (K+1) p).seven.digit = 2 := by
    simpa [Nat.add_assoc] using hOverlap.2

  have hNotHappy :
      ¬ HappyCell
        (graph 1 (K+1) p).seven.carry
        (graph 1 (K+1) p).seven.digit := by
    intro hHappy
    apply hNoRelocated
    exact ⟨p, hp, hHappy⟩

  have hCarryLt : (graph 1 (K+1) p).seven.carry < 4 :=
    graph_carry_lt_four 1 (K+1) p

  have hCarryNeZero : (graph 1 (K+1) p).seven.carry ≠ 0 := by
    intro h0
    apply hNotHappy
    exact ⟨hdNext, Or.inl h0⟩

  have hCarryNeThree : (graph 1 (K+1) p).seven.carry ≠ 3 := by
    intro h3
    apply hNotHappy
    exact ⟨hdNext, Or.inr h3⟩

  have hMiddle :
      (graph 1 (K+1) p).seven.carry = 1 ∨
      (graph 1 (K+1) p).seven.carry = 2 := by
    omega

  have hRec := (graph_cell_exact 1 (K+1) p).2
  have hNextCarry : (graph 1 (K+1) (p+1)).seven.carry = 3 := by
    rcases hMiddle with h1 | h2
    · simpa [h1, hdNext, GST2DMixedEmergence.nextCarry] using hRec.symm
    · simpa [h2, hdNext, GST2DMixedEmergence.nextCarry] using hRec.symm

  exact ⟨hdNext, hMiddle, hNextCarry⟩

#check fresh_failed_edge_forces_latent_seed
#print axioms fresh_failed_edge_forces_latent_seed

end Task33FreshPowerPropagation
