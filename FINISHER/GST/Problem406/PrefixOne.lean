import ErdosTernary2

/-!
# Prefix-one bridge API

Public names for the bridge carrying four-power creation certificates into the
prefix-one navigation layer.
-/

namespace GST
namespace Problem406

/-- Public name for the prefix-one navigation lifting proposition. -/
abbrev PrefixOneNavigationLift : Prop := GSTPrefixOneNavigationLift

/-- Public name for the four-power creation master proposition. -/
abbrev FourPowerCreationMaster : Prop := GSTFourPowerOntologicalAdapter.FourPowerCreationMaster

/-- The four-power creation master certified inside the monolith. -/
theorem four_power_creation_master : FourPowerCreationMaster := by
  exact gst_four_power_creation_master_inline

/-- A creation master supplies the prefix-one navigation lift. -/
abbrev prefix_one_navigation_lift_of_creation_master :=
  gst_prefix_one_navigation_lift_of_master_inline

/-- Certified public prefix-one navigation lift. -/
theorem prefix_one_navigation_lift : PrefixOneNavigationLift := by
  exact gst_prefix_one_navigation_lift

/-- Terminal Step-6 packet exported under a neutral reviewer-facing name. -/
abbrev terminal_step_six_packet :=
  gst_step6_terminal_packet_kernel

end Problem406
end GST
