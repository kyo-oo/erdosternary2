import ErdosTernary2

/-!
# Navigation API

Public names for the monolith's navigation witness and finite endpoint bridge.
-/

namespace GST
namespace Problem406

/-- Public name for the monolith navigation witness. -/
abbrev NavigationWitness : Nat → Prop := GSTNavigationWitness

/-- Canonical standalone navigation gives the monolith navigation witness. -/
theorem navigation_witness_of_canonical_navigation :
    _ := by
  exact gst_navigation_witness_of_standalone_navigation

/-- Finite endpoint adapter for the BIG-N seed-three branch. -/
theorem bigN_seed_three_endpoint_forces_non_one :
    _ := by
  exact gst_bigN_seed3_endpoint_forces_non_one_inline

/-- Finite-support horizon for the canonical child information. -/
theorem prefix_one_bigN_future_zero :
    _ := by
  exact gst_prefix_one_bigN_future_zero_inline

end Problem406
end GST
