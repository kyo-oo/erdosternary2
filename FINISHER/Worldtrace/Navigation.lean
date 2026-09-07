import ErdosTernary2
import GST.Problem406.Navigation

/-!
# Worldtrace navigation layer

Public names for the navigation constants, graph positions, origin fingerprints,
and General Space Theory witness transport.  General Space Theory remains the
navigation-geometric pillar inside Worldtrace Arithmetic.
-/

namespace Worldtrace
namespace Navigation

/-- Navigation constant attached to the power `4^(3^s * b)`. -/
abbrev Constant : Nat → Nat → Nat := _root_.gstNavigationConstant

/-- Navigation witness predicate used by the proof stack. -/
abbrev Witness : Nat → Prop := GST.Problem406.NavigationWitness

/-- Graph witness in the full bounded power graph. -/
abbrev GraphWitness : Nat → Nat → Nat → Prop := _root_.GSTGraphWitness

/-- Exact navigation decomposition of a power into origin plus ternary tail. -/
abbrev decomposition := _root_.gst_navigation_decomposition

/-- Orthogonal split: origin, created tail, and finite prefix are kept together. -/
abbrev orthogonal_origin_split := _root_.gst_orthogonal_origin_split

/-- Every finite graph prefix is encoded in the corresponding perfect-power residue. -/
abbrev orthogonal_origin_fingerprint := _root_.gst_orthogonal_origin_fingerprint

/-- Bad-trace system coupled to origin fingerprints. -/
abbrev orthogonal_bad_trace_system := _root_.gst_orthogonal_badTrace_system

/-- Exact recurrence for the residue-one branch. -/
abbrev constant_b1_recurrence := _root_.gst_navigation_constant_b1_recurrence

/-- General recurrence for a ternary wave-depth cut. -/
abbrev constant_general_recurrence := _root_.gst_navigation_constant_general_recurrence

/-- Standalone canonical navigation implies the public navigation witness. -/
abbrev witness_of_canonical_navigation := GST.Problem406.navigation_witness_of_canonical_navigation

/-- Finite endpoint adapter for the seed-three branch. -/
abbrev bigN_seed_three_endpoint_forces_non_one := GST.Problem406.bigN_seed_three_endpoint_forces_non_one

/-- Finite-support horizon for canonical child information. -/
abbrev prefix_one_bigN_future_zero := GST.Problem406.prefix_one_bigN_future_zero

/-- Exact digit transport from the power tail to the navigation constant. -/
abbrev digit_shift := _root_.gst_navigation_digit_shift

/-- Exact carry transport from the power tail to the navigation constant. -/
abbrev carry_shift := _root_.gst_navigation_carry_shift

/-- Space classification transport from the power tail to the navigation constant. -/
abbrev space_shift := _root_.gst_navigation_space_shift

/-- Universal shifted equivalence between full-power positions and navigation positions. -/
abbrev position_universal := _root_.gst_navigation_position_universal

/-- Lift one Happy-gate vertex into the bounded seven-axis graph. -/
abbrev graph_lift := _root_.gst_navigation_graph_lift

/-- Explicit first cascade branch navigation position. -/
abbrev position_b2 := _root_.gst_navigation_position_b2

/-- Explicit first cascade branch graph witness. -/
abbrev graph_b2 := _root_.gst_navigation_graph_b2

end Navigation
end Worldtrace
