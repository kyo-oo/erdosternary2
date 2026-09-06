import ErdosTernary2
import GST.Arithmetic.Carries

/-!
# Worldtrace carry-information layer

Public names for exact carry transport, affine carry state, and prefix survival.
This is the information-flow layer connecting ternary events to navigation and
collision arguments.
-/

namespace Worldtrace
namespace Carry

/-- Early structural carry at position `p` when computing `4 * R`. -/
abbrev structuralCarry : Nat → Nat → Nat := _root_.carryAtPos

/-- Physical carry at position `p` in the navigation/collision layers. -/
abbrev carry : Nat → Nat → Nat := _root_.gstCarry

/-- Ternary digit at position `p` in the navigation/collision layers. -/
abbrev digit : Nat → Nat → Nat := _root_.gstDigit

/-- Space classification induced by a carry state. -/
abbrev spaceAt : Nat → Nat → _root_.GSTSpace := _root_.gstSpaceAt

/-- Seeded affine carry used to preserve incoming information across a cut. -/
abbrev affineCarry : Nat → Nat → Nat → Nat → Nat := _root_.gstAffineMulCarry

/-- Structural carry is bounded by four. -/
theorem structural_carry_bound := _root_.carryAtPos_bound

/-- Row-one structural carry for residue zero. -/
theorem structural_carry_one_of_mod_three_zero := _root_.carryAtPos_one_mod3_0

/-- Row-one structural carry for residue one. -/
theorem structural_carry_one_of_mod_three_one := _root_.carryAtPos_one_mod3_1

/-- Row-one structural carry for residue two. -/
theorem structural_carry_one_of_mod_three_two := _root_.carryAtPos_one_mod3_2

/-- A visible residue-two digit survives multiplication by four. -/
theorem digit_two_survives_times_four := _root_.gst_decide_survival

/-- Exact carry-forward law including position zero. -/
theorem carry_forward_exact := _root_.gstCarry_forward_exact_all

/-- Public wrapper for the canonical x4 carry bound. -/
theorem carry_lt_four := GST.Arithmetic.carry4_lt_four

/-- Exact one-column carry-forward law for public x4 carries. -/
theorem carry4_forward_exact := GST.Arithmetic.carry4_forward_exact

/-- Affine prefix carry survives every low cut below the injected tail. -/
theorem affine_prefix_carry := _root_.gst_affine_prefix_carry

/-- Affine prefix digit survives every strict low cut below the injected tail. -/
theorem affine_prefix_digit := _root_.gst_affine_prefix_digit

/-- A digit-two plus/null witness survives a protected affine prefix. -/
theorem affine_prefix_witness := _root_.gst_affine_prefix_witness

/-- Seeded affine carry composes under a ternary cut. -/
theorem seeded_affine_carry_semigroup := _root_.gst_seeded_affine_carry_semigroup

/-- Seeded affine digits shift under a ternary cut. -/
theorem seeded_affine_digit_shift := _root_.gst_seeded_affine_digit_shift

/-- Bad traces shift through a seeded affine cut. -/
theorem seeded_affine_bad_shift := _root_.gst_seeded_affine_bad_shift

/-- Child carry reindexing after a ternary cut. -/
theorem child_carry_reindex_seeded := _root_.gst_child_carry_reindex_seeded

/-- Full child digit/carry state reindexing. -/
theorem child_state_reindex_seeded := _root_.gst_child_state_reindex_seeded

/-- Full parent seeded-affine state reindexing. -/
theorem parent_state_reindex_seeded := _root_.gst_parent_state_reindex_seeded

/-- A child Happy gate localizes to position zero after cutting at its row. -/
theorem child_gate_reindex_seeded := _root_.gst_child_gate_reindex_seeded

/-- Exact block-memory identity for an affine carrier. -/
theorem affine_block_memory := _root_.gst_affine_block_memory

/-- Conserved carry equation connecting child, parent, and affine realizations. -/
theorem shared_information_carry_equation := _root_.gst_shared_information_carry_equation

/-- An affine information carry remains inside its multiplier interval. -/
theorem affine_carry_lt_multiplier := _root_.gst_affine_carry_lt_multiplier

end Carry
end Worldtrace
