import GSTFinalPrefixOneDirectU2DCollision
import GSTGraphV2PerfectPowerAncestry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTPrefixOneDirectNavigationLift

open GSTCanonicalTailStateIso
open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2HandwrittenOmegaUBlock
open GSTPerfectPowerTailNavigation

/-- Unconditional kernel-level prefix-one Navigation lift.

A hypothetical failure of the parent canonical tail makes the entire physical
right edge of the exact residual perfect-power block bad.  The certified
all-depth U2D collision then contradicts the supplied child Navigation. -/
theorem canonical_prefix_one_navigation_lift
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : Navigation (canonicalTail (s+1) n)) :
    Navigation (canonicalTail s (1 + 3*n)) := by
  by_contra hNoParent

  have hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit := by
    intro j hRight

    have hAbs :
        GSTU2DEventTransport.HappyCell
          (graph 1 (residualParentExponent s 1 n) (s+2+j)).seven.carry
          (graph 1 (residualParentExponent s 1 n) (s+2+j)).seven.digit :=
      (residual_parent_happy_iff s 1 n (s+2+j)).1 hRight

    have hPhysical :
        GSTCanonicalTailStateIso.HappyCell
          (GSTCanonicalTailStateIso.carry4
            (4^(3^s * (1 + 3*n))) (s+2+j))
          (GSTCanonicalTailStateIso.digit3
            (4^(3^s * (1 + 3*n))) (s+2+j)) := by
      simpa [GSTGraphV2InfiniteControl.graph,
        GSTGraphV2InfiniteControl.cell,
        GSTCanonicalSevenAxisBridge.vertex,
        GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent,
        GSTU2DEventTransport.HappyCell,
        GSTCanonicalTailStateIso.HappyCell,
        GSTCanonicalSevenAxisBridge.carry4,
        GSTCanonicalTailStateIso.carry4,
        GSTCanonicalSevenAxisBridge.digit3,
        GSTCanonicalTailStateIso.digit3,
        Nat.pow_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAbs

    have hDecomp := canonical_tail_decomposition s (1 + 3*n)
    rw [hDecomp] at hPhysical

    have hTail :
        GSTCanonicalTailStateIso.HappyCell
          (GSTCanonicalTailStateIso.carry4
            (canonicalTail s (1+3*n)) (1+j))
          (GSTCanonicalTailStateIso.digit3
            (canonicalTail s (1+3*n)) (1+j)) := by
      apply (canonical_tail_happy_iff
        (s+1) (canonicalTail s (1+3*n)) (1+j) (by omega)).1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hPhysical

    apply hNoParent
    exact ⟨1+j, hTail⟩

  exact
    (GSTFinalPrefixOneDirectU2DCollision.canonical_right_bad_forces_no_child_navigation
      s n hs hn hRightBad) hchild

#check canonical_prefix_one_navigation_lift
#print axioms canonical_prefix_one_navigation_lift

end GSTPrefixOneDirectNavigationLift
