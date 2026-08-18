import ErdosTernary2
import CanonicalOriginTritForcingScratch
import CanonicalResidualInfiniteSupportBridgeScratch

/- CI probe for the isolated 2026-08-18 GST V2 atomic surgery branch.
   This deliberately adds no axiom, sorry, admit, native_decide, or proof shortcut.
   The goal is to force the latest Sol canonical-origin layer through the kernel
   together with the active production monolith. -/

#check gst_prefix_one_bad_good_big2_prefix_forces_origin_nonzeroS
#check GSTCanonicalResidualInfiniteSupportBridgeS
#check gst_last_child_gate_right_chordS

example (n : Nat) : n = n := rfl
