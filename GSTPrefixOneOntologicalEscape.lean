import GSTPerfectPowerTailNavigation
import GSTFourPowerOntologicalAdapter
import GSTFourPowerDirectExistence
import GSTFourPowerDirectCreationMaster
import GSTFourPowerDirectHappyBridge
import GSTFourPowerDirectFailedRelocationState
import GSTFourPowerDirectExistenceProviderPipeline
import GSTFourPowerDirectExistenceNoAxiom

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

/-- POE — Prefix-One Ontological Escape, exactly downstream of a supplied
four-power creation master.  The theorem is deliberately conditional: this
file no longer imports the unresolved infinite-navigation collision provider
just to manufacture the historical inline boundary. -/
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
This is the no-axiom route into the prefix-one seam once a closed provider is
available; it does not force the experimental infinite-navigation module into
the repository build. -/
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
the direct prefix-engine route: universal prefix hits give row-three-or-higher
`CommonTwo`, then physical Happy cells, then creation certificates. -/
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

/-- Public direct-existence route from the Chat-2 affine automaton target.
This is the replacement public seam for the deleted historical inline axiom:
prove the concrete no-bad-channel theorem, and direct four-power existence
follows without importing the infinite collision provider. -/
theorem gst_four_power_direct_existence_from_no_bad_affine_channel_one
    (hNoBad : GSTFourPowerDirectExistenceProviderPipeline.FourPowerDirectNoBadAffineChannelOne) :
    GSTFourPowerDirectExistence.FourPowerDirectExistence := by
  exact
    GSTFourPowerDirectExistenceProviderPipeline.fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
      hNoBad

/-- Public direct-existence route from the parametric prefix-hit theorem. -/
theorem gst_four_power_direct_existence_from_prefixHitGeThree
    (hProvider : ∀ K : Nat, 8 ≤ K → GSTFourPowerHappyProvider.PrefixHitGeThree K) :
    GSTFourPowerDirectExistence.FourPowerDirectExistence := by
  exact
    GSTFourPowerDirectExistenceNoAxiom.fourPowerDirectExistence_from_physical_happy_ge_three
      (fun K hK =>
        GSTFourPowerHappyProvider.four_power_happy_ge_three_from_prefixHitGeThree
          hProvider K hK)

#check gst_four_power_creation_certificate_noAxiom_from_provider
#check gst_four_power_creation_certificate_noAxiom_from_commonTwoGeThree
#check gst_four_power_creation_certificate_noAxiom_from_prefixHitGeThree
#check gst_four_power_creation_certificate_noAxiom_from_no_bad_affine_channel_one
#check gst_four_power_direct_existence_from_no_bad_affine_channel_one
#check gst_four_power_direct_existence_from_prefixHitGeThree
#print axioms gst_four_power_creation_certificate_noAxiom_from_provider
#print axioms gst_four_power_creation_certificate_noAxiom_from_commonTwoGeThree
#print axioms gst_four_power_creation_certificate_noAxiom_from_prefixHitGeThree
#print axioms gst_four_power_creation_certificate_noAxiom_from_no_bad_affine_channel_one
#print axioms gst_four_power_direct_existence_from_no_bad_affine_channel_one
#print axioms gst_four_power_direct_existence_from_prefixHitGeThree
