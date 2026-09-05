import GSTPerfectPowerTailNavigation
import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectExistence
import GSTFourPowerDirectCreationMaster
import GSTFourPowerDirectHappyBridge
import GSTFourPowerDirectFailedRelocationState
import GSTFourPowerDirectExistenceProviderPipeline

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPrefixOneOntologicalEscape

open GSTCanonicalTailStateIso
open GSTPerfectPowerTailNavigation
open GSTFourPowerOntologicalAdapter

/-- Prefix-one exponents enter the four-power range automatically. -/
theorem prefix_one_exponent_ge_twelve
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    12 ≤ 3^s * (1 + 3*n) := by
  have h3s : 3 ≤ 3^s := by
    simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hs)
  have hb : 4 ≤ 1 + 3*n := by omega
  nlinarith

/-- POE — Prefix-One Ontological Escape, exactly downstream of the four-power
creation master.  No child witness occurs. -/
theorem gst_prefix_one_ontological_escape_of_master
    (hMaster : FourPowerCreationMaster)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    Navigation (canonicalTail s (1 + 3*n)) := by
  let K : Nat := 3^s * (1 + 3*n)
  have hK12 : 12 ≤ K := by
    dsimp [K]
    exact prefix_one_exponent_ge_twelve s n hs hn
  have hFull : Navigation (4^K) :=
    gst_four_power_ontological_navigation_of_master hMaster K (by omega) (by omega)
  exact canonical_tail_projection s (1 + 3*n) hs (by simpa [K] using hFull)

end GSTPrefixOneOntologicalEscape

/-- Monolith transplant entrypoint from the checked physical Happy provider.
This is the no-axiom route into the old prefix-one seam: once the provider is
available, the historical creation-certificate name is produced by the checked
four-power provider pipeline rather than by the legacy inline axiom. -/
theorem gst_four_power_creation_certificate_noAxiom_from_provider
    (hProvider : GSTFourPowerDirectExistenceProviderPipeline.FourPowerHappyGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    GSTFourPowerDirectExistenceProviderPipeline.fourPowerCreationCertificate_noAxiom_from_provider
      hProvider K hK5 hK7

/-- Monolith transplant entrypoint from the row-three-or-higher common-two
provider. -/
theorem gst_four_power_creation_certificate_noAxiom_from_commonTwoGeThree
    (hProvider : GSTFourPowerDirectExistenceProviderPipeline.FourPowerCommonTwoGeThreeProvider)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    GSTFourPowerDirectExistenceProviderPipeline.fourPowerCreationCertificate_noAxiom_from_commonTwoGeThree
      hProvider K hK5 hK7

/-- Monolith transplant entrypoint from the parametric prefix-hit law.  This is
where the newly accepted prefix engine enters the production seam: a universal
`PrefixHitGeThree` provider gives the physical Happy provider, then the direct
existence and creation-certificate bridge close through the checked pipeline. -/
theorem gst_four_power_creation_certificate_noAxiom_from_prefixHitGeThree
    (hProvider : ∀ K : Nat, 8 ≤ K → GSTFourPowerHappyProvider.PrefixHitGeThree K)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    GSTFourPowerDirectExistenceProviderPipeline.fourPowerCreationCertificate_noAxiom_from_provider
      (fun L hL =>
        GSTFourPowerHappyProvider.four_power_happy_ge_three_from_prefixHitGeThree
          hProvider L hL)
      K hK5 hK7

/-- Monolith transplant entrypoint from the Chat-2 bad-affine-channel kill
formulation. -/
theorem gst_four_power_creation_certificate_noAxiom_from_no_bad_affine_channel_one
    (hNoBad : GSTFourPowerDirectExistenceProviderPipeline.FourPowerDirectNoBadAffineChannelOne)
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    GSTFourPowerDirectExistenceProviderPipeline.fourPowerCreationCertificate_noAxiom_from_no_bad_affine_channel_one
      hNoBad K hK5 hK7

/-- Explicit production boundary for the still-open direct universal existence
law.  Kept out of the obsolete infinite-navigation provider so the committed
production closure can build and the comparator can certify the current seam. -/
axiom gst_four_power_direct_existence_inline :
    GSTFourPowerDirectExistence.FourPowerDirectExistence

/-- Root-level compatibility name consumed by the monolith tail.  It no longer
imports or compiles the experimental infinite-navigation/collision route; it
routes the old certificate API through the direct creation-master bridge. -/
theorem gst_four_power_creation_certificate_inline
    (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) := by
  exact
    (GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
      gst_four_power_direct_existence_inline) K hK5 hK7

#check gst_four_power_creation_certificate_noAxiom_from_provider
#check gst_four_power_creation_certificate_noAxiom_from_commonTwoGeThree
#check gst_four_power_creation_certificate_noAxiom_from_prefixHitGeThree
#check gst_four_power_creation_certificate_noAxiom_from_no_bad_affine_channel_one
#print axioms gst_four_power_creation_certificate_noAxiom_from_provider
#print axioms gst_four_power_creation_certificate_noAxiom_from_commonTwoGeThree
#print axioms gst_four_power_creation_certificate_noAxiom_from_prefixHitGeThree
#print axioms gst_four_power_creation_certificate_noAxiom_from_no_bad_affine_channel_one
#print axioms gst_four_power_direct_existence_inline
#print axioms gst_four_power_creation_certificate_inline
