import GSTCanonicalCarryDynamics
import GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTFourPowerOntologicalAdapter

open GSTCanonicalTailStateIso
open GSTCanonicalCarryDynamics

/-- Historical CREATE certificate, stated without any monolith dependency. -/
def CreationCertificate (R : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧ R / 3^p % 3 = 2 ∧
    ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
     ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧
      R / 3^(p+1) % 3 = 2))

/-- Navigation-Creation Equivalence, forward direction used by FP-NAV.
The second CREATE branch advances one exact x4 carry edge from carry one to carry three. -/
theorem creation_certificate_to_navigation
    (R : Nat) (hCreate : CreationCertificate R) : Navigation R := by
  obtain ⟨p, hp, hdRaw, hcase⟩ := hCreate
  have hd : digit3 R p = 2 := by
    simpa [digit3] using hdRaw
  have hClt : carry4 R p < 4 := carry4_lt_four R p
  rcases hcase with hzero | hone
  · have hCmod : carry4 R p % 3 = 0 := by
      simpa [carry4] using hzero
    have hC : carry4 R p = 0 ∨ carry4 R p = 3 := by omega
    exact ⟨p, hd, hC⟩
  · have hCmod : carry4 R p % 3 = 1 := by
      simpa [carry4] using hone.1
    have hC : carry4 R p = 1 := by
      have hmodlt : carry4 R p % 3 < 3 := Nat.mod_lt _ (by decide)
      omega
    have hnext := carry4_forward_exact R p
    have hCnext : carry4 R (p+1) = 3 := by
      rw [hC, hd] at hnext
      norm_num at hnext
      exact hnext
    have hdnext : digit3 R (p+1) = 2 := by
      simpa [digit3] using hone.2
    exact ⟨p+1, hdnext, Or.inr hCnext⟩

/-- The existing independent universal four-power certificate is exactly a
`CreationCertificate` in the new standalone language. -/
theorem four_power_creation_certificate
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    CreationCertificate (4^K) := by
  simpa [CreationCertificate] using
    (GSTInfiniteFourPowerNavigation.gst_four_power_navigation_universal K hK5 hK7)

/-- FP-NAV: the independent four-power theorem gives physical Graph-V2 Navigation. -/
theorem gst_four_power_ontological_navigation_master
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    Navigation (4^K) :=
  creation_certificate_to_navigation (4^K)
    (four_power_creation_certificate K hK5 hK7)

end GSTFourPowerOntologicalAdapter
