import GSTFourPowerOntologicalAdapter

/-!
# Four-power certificate API

Public certificate names connecting direct arithmetic witnesses to physical
navigation. This layer is a wrapper only.
-/

namespace GST
namespace FourPower

/-- Historical creation certificate for a number `R`. -/
abbrev CreationCertificate : Nat → Prop := GSTFourPowerOntologicalAdapter.CreationCertificate

/-- Universal four-power creation master proposition. -/
abbrev CreationMaster : Prop := GSTFourPowerOntologicalAdapter.FourPowerCreationMaster

/-- A creation certificate gives a navigation witness. -/
theorem creation_certificate_to_navigation
    (R : Nat) (h : CreationCertificate R) : GSTCanonicalTailStateIso.Navigation R := by
  exact GSTFourPowerOntologicalAdapter.creation_certificate_to_navigation R h

/-- Four-power navigation from a supplied creation master. -/
theorem four_power_navigation_of_master
    (hMaster : CreationMaster)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTCanonicalTailStateIso.Navigation (4^K) := by
  exact GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master hMaster K hK5 hK7

end FourPower
end GST
