import GSTGraphV2TransparentWidthThree

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalTransparentBridgeProbe

open GSTCanonicalSevenAxisBridge
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2TransparentWidthThree
open GSTU2DEventTransport

/-- Every positive canonical width is an exact integer number of transparent
width-three blocks. -/
theorem canonicalWidth_eq_three_mul
    (s : Nat) (hs : 1 ≤ s) :
    ∃ r : Nat, canonicalWidth s = 3 * 3^r := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs
  refine ⟨r, ?_⟩
  simp [canonicalWidth, pow_add]

/-- A Happy cell at the canonical child boundary propagates, through the
literal transparent width-three Graph-V2 mechanism, to a Happy cell on the
canonical right boundary.  No support horizon or terminal-row assumption is
used. -/
theorem canonical_child_happy_forces_right_happy_transparent
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit) :
    ∃ j : Nat, HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit := by
  obtain ⟨r, hWidth⟩ := canonicalWidth_eq_three_mul s hs

  have hChildAbs : HappyCell
      (carry4 (4^(3^(s+1) * n)) (s+2+q))
      (digit3 (4^(3^(s+1) * n)) (s+2+q)) := by
    have hAbs :=
      (canonical_power_origin_happy_iff s n 0 (s+2+q)).mp hChild
    simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hAbs

  obtain ⟨j, hj⟩ :=
    power_happy_add_three_mul_at_cut
      (3^(s+1) * n) (s+2) q (3^r) hChildAbs

  have hAbsRight : HappyCell
      (graph 1 (3^(s+1) * n + 3 * 3^r) (s+2+j)).seven.carry
      (graph 1 (3^(s+1) * n + 3 * 3^r) (s+2+j)).seven.digit := by
    simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hj

  rw [← hWidth] at hAbsRight
  exact
    (canonical_power_origin_happy_iff
      s n (canonicalWidth s) (s+2+j)).mpr hAbsRight

/-- The canonical child-Happy / all-depth-right-bad packet is inconsistent.
This is the direct canonical perfect-power block collision obtained by
iterating the transparent Graph-V2 width-three conservation mechanism. -/
theorem canonical_transparent_block_collision
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit)
    (hRightBad : ∀ j : Nat, ¬ HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit) :
    False := by
  obtain ⟨j, hj⟩ :=
    canonical_child_happy_forces_right_happy_transparent s n q hs hChild
  exact hRightBad j hj

#check canonicalWidth_eq_three_mul
#check canonical_child_happy_forces_right_happy_transparent
#check canonical_transparent_block_collision
#print axioms canonical_child_happy_forces_right_happy_transparent
#print axioms canonical_transparent_block_collision

end GSTGraphV2CanonicalTransparentBridgeProbe
