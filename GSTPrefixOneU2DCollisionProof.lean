import GSTGraphV2InfiniteControl
import GSTGraphV2HandwrittenExponentialLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPrefixOneU2DCollisionProof

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialLTE

/-- Canonical child full power used by the prefix-one descent seam. -/
def childEnergy (s n : Nat) : Nat := 4^(3^(s+1) * n)

/-- Tail exposed at the production cut `s+2`. -/
def childTail (s n : Nat) : Nat := childEnergy s n / 3^(s+2)

/-- The pure child power has literal low prefix one at the production cut. -/
theorem child_energy_decomposition (s n : Nat) :
    childEnergy s n = 1 + 3^(s+2) * childTail s n := by
  have hmod : childEnergy s n % 3^(s+2) = 1 := by
    dsimp [childEnergy]
    simpa [Nat.add_assoc] using
      (pow4_scaled_mod_next (s+1) n)
  have hsplit := (Nat.mod_add_div (childEnergy s n) (3^(s+2))).symm
  rw [hmod] at hsplit
  simpa [childTail] using hsplit

/-- First production adapter: a Happy gate of the quotient child is literally
    a Happy cell on the full-power graph at vertical coordinate `s+2+q`. -/
theorem child_tail_happy_to_graph
    (s n q : Nat) (hs : 1 ≤ s)
    (hHappy : HappyCell (carry4 (childTail s n) q) (digit3 (childTail s n) q)) :
    HappyCell
      (graph (childEnergy s n) 0 (s+2+q)).seven.carry
      (graph (childEnergy s n) 0 (s+2+q)).seven.digit := by
  have hE :
      4^0 * childEnergy s n = 1 + 3^(s+2) * childTail s n := by
    simpa using child_energy_decomposition s n
  have hpow : 3^3 ≤ 3^(s+2) := by
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hP : 1 < 3^(s+2) := by omega
  have h4 : 4 < 3^(s+2) := by
    norm_num at hpow ⊢
    omega
  have hiff :=
    graph_prefix_slice_happy_iff
      (childEnergy s n) 0 (s+2) 1 (childTail s n) q hE hP
  apply hiff.mpr
  rcases hHappy with ⟨hd, hc⟩
  constructor
  · exact hd
  · have hseed : (4 * 1) / 3^(s+2) = 0 := Nat.div_eq_of_lt (by simpa using h4)
    simpa [hseed, seededCarry, carry4] using hc

#print axioms child_energy_decomposition
#print axioms child_tail_happy_to_graph

end GSTPrefixOneU2DCollisionProof
