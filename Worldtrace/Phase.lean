import ErdosTernary2
import Worldtrace.Carry

/-!
# Worldtrace phase-cycle layer

Public names for NULL regeneration, seed cycling, and conserved shared
information.  This layer is the formal bridge between local carry phases and
infinite/terminal obstruction behavior.
-/

namespace Worldtrace
namespace Phase

/-- NULL is not terminal: a carry-zero digit-two cell regenerates nonzero carry. -/
theorem null_two_regenerates := _root_.gst_null_two_regenerates

/-- A carry-three digit-two cell propagates the carry-three phase. -/
theorem plus_two_propagates := _root_.gst_plus_two_propagates

/-- Conserved carry equation connecting child, parent, and affine realizations. -/
theorem shared_information_carry_equation := _root_.gst_shared_information_carry_equation

/-- Generic seeded commuting-square law. -/
theorem seeded_shared_information_equation := _root_.gst_seeded_shared_information_equationS

/-- Phase 0 to phase 1: seed zero becomes seed one. -/
theorem phase_zero_to_one_shared_information := _root_.gst_phase01_shared_informationS

/-- Phase 1 to phase 2: seed one becomes seed two. -/
theorem phase_one_to_two_shared_information := _root_.gst_phase12_shared_informationS

/-- Phase 2 to the next phase 0: the seed wraps without dying. -/
theorem phase_two_to_zero_shared_information := _root_.gst_phase20_shared_informationS

/-- The three companion offsets remain inside the same multiplier interval. -/
theorem phase_cycle_offsets_inside := _root_.gst_phase_cycle_offsets_insideS

/-- A complete seeded bad trace can be cut at any ternary position. -/
theorem seeded_bad_trace_suffix := _root_.gst_seeded_bad_trace_suffixS

/-- A seeded child Happy gate becomes a position-zero Happy gate after cutting. -/
theorem seeded_gate_localizes := _root_.gst_seeded_gate_localizesS

/-- Cutting a relative affine realization keeps the same relative multiplier. -/
theorem relative_affine_suffix := _root_.gst_relative_affine_suffixS

end Phase
end Worldtrace
