import GSTGraphV2SleepEquationLabScratch
import GSTGraphV2InfiniteOriginWorldCollisionScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Sleep-equation finite-origin collision

The readable handwritten three-world term is

  K(q) = 5 * sum_{j<q} (2^j * 3^j).

The sleep-equation laboratory proves K(q)=6^q-1 at every natural q.  Hence an
ordinary finite natural origin cannot agree with K(q) at all scales, or even at
cofinally many scales.
-/

def gstSleepJoinedWorldCodeS (q : Nat) : Nat :=
  5 * Finset.sum (Finset.range q) (fun j => 2^j * 3^j)

/-- Exact closed form of the joined handwritten world code. -/
theorem gst_sleep_joined_world_code_closedS (q : Nat) :
    gstSleepJoinedWorldCodeS q = 6^q - 1 := by
  exact gst_sleep_weighted_join_sumS q

/-- No finite natural can equal the handwritten joined-world code modulo every
6^q world. -/
theorem gst_sleep_no_finite_origin_all_scalesS (n : Nat) :
    ¬ (∀ q, n % 6^q = gstSleepJoinedWorldCodeS q) := by
  intro h
  apply gst_natural_origin_not_maximal_in_all_six_worldsS n
  intro q
  rw [gst_sleep_joined_world_code_closedS]
  exact h q

/-- Cofinal agreement is already impossible: after every requested cutoff one
cannot find a later six-world where a finite origin equals the handwritten
maximal joined-world code. -/
theorem gst_sleep_no_finite_origin_cofinalS (n : Nat) :
    ¬ (∀ M, ∃ q, M ≤ q ∧ n % 6^q = gstSleepJoinedWorldCodeS q) := by
  intro hcofinal
  obtain ⟨q, hq, heq⟩ := hcofinal (n+1)
  rw [gst_sleep_joined_world_code_closedS] at heq
  have hqpow : q < 6^q := Nat.lt_pow_self (by decide : 1 < 6)
  have hnlt : n < 6^q := by omega
  rw [Nat.mod_eq_of_lt hnlt] at heq
  have hp : 0 < 6^q := Nat.pow_pos (by decide)
  omega

/-- Strong cutoff form.  From world n+1 onward the finite origin is separated
from the handwritten joined-world code at every scale. -/
theorem gst_sleep_finite_origin_cutoffS (n q : Nat) (hq : n+1 ≤ q) :
    n % 6^q ≠ gstSleepJoinedWorldCodeS q := by
  intro heq
  rw [gst_sleep_joined_world_code_closedS] at heq
  have hqpow : q < 6^q := Nat.lt_pow_self (by decide : 1 < 6)
  have hnlt : n < 6^q := by omega
  rw [Nat.mod_eq_of_lt hnlt] at heq
  have hp : 0 < 6^q := Nat.pow_pos (by decide)
  omega

#check gst_sleep_no_finite_origin_all_scalesS
#check gst_sleep_no_finite_origin_cofinalS
#check gst_sleep_finite_origin_cutoffS

#print axioms gst_sleep_no_finite_origin_cofinalS

end GSTInfiniteV2
