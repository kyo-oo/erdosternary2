import ErdosTernary2
import GST.FourPower.Certificate
import GST.Problem406.PrefixOne
import GST.Problem406.LocalCell

/-!
# Worldtrace finite certificate layer

Public names for certified local gates, creation certificates, prefix-one bridge
certificates, and kernel-decidable terminal closures.  This module collects the
finite evidence layer without hiding the larger proof corpus.
-/

namespace Worldtrace
namespace Certificate

/-- Historical creation certificate for a number `R`. -/
abbrev CreationCertificate : Nat → Prop := GST.FourPower.CreationCertificate

/-- Universal four-power creation master proposition. -/
abbrev CreationMaster : Prop := GST.FourPower.CreationMaster

/-- Prefix-one navigation lifting proposition. -/
abbrev PrefixOneNavigationLift : Prop := GST.Problem406.PrefixOneNavigationLift

/-- Four-power creation master proposition. -/
abbrev FourPowerCreationMaster : Prop := GST.Problem406.FourPowerCreationMaster

/-- A creation certificate gives a navigation witness. -/
abbrev creation_certificate_to_navigation := GST.FourPower.creation_certificate_to_navigation

/-- Four-power creation master certified inside the proof corpus. -/
abbrev four_power_creation_master := GST.Problem406.four_power_creation_master

/-- A creation master supplies the prefix-one navigation lift. -/
abbrev prefix_one_navigation_lift_of_creation_master := GST.Problem406.prefix_one_navigation_lift_of_creation_master

/-- Certified prefix-one navigation lift. -/
abbrev prefix_one_navigation_lift := GST.Problem406.prefix_one_navigation_lift

/-- Terminal Step-6 packet exported under a neutral reviewer-facing name. -/
abbrev terminal_step_six_packet := GST.Problem406.terminal_step_six_packet

/-- Exact local hand-off at the last child Happy gate. -/
abbrev last_child_gate_right_chord := GST.Problem406.last_child_gate_right_chord

/-- Explicit low-level terminal base for level one. -/
abbrev residual_null_terminal_happy_s1 := _root_.gst_residual_null_terminal_happy_s1S

/-- Explicit low-level terminal base for level two. -/
abbrev residual_null_terminal_happy_s2 := _root_.gst_residual_null_terminal_happy_s2S

/-- Explicit low-level terminal base for level three. -/
abbrev residual_null_terminal_happy_s3 := _root_.gst_residual_null_terminal_happy_s3S

/-- Uniform terminal certificate for all positive canonical levels. -/
abbrev residual_null_terminal_happy_all := _root_.gst_residual_null_terminal_happy_allS

end Certificate
end Worldtrace
