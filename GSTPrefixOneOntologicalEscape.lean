import GSTPerfectPowerTailNavigation
import GSTFourPowerOntologicalAdapter

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPrefixOneOntologicalEscape

open GSTCanonicalTailStateIso
open GSTPerfectPowerTailNavigation
open GSTFourPowerOntologicalAdapter

/-- Prefix-one exponents enter the independent four-power range automatically. -/
theorem prefix_one_exponent_ge_twelve
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    12 ≤ 3^s * (1 + 3*n) := by
  have h3s : 3 ≤ 3^s := by
    simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hs)
  have hb : 4 ≤ 1 + 3*n := by omega
  nlinarith

/-- POE — Prefix-One Ontological Escape.
For every `s,n ≥ 1`, the canonical parent tail navigates unconditionally. -/
theorem gst_prefix_one_ontological_escape
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    Navigation (canonicalTail s (1 + 3*n)) := by
  let K : Nat := 3^s * (1 + 3*n)
  have hK12 : 12 ≤ K := by
    dsimp [K]
    exact prefix_one_exponent_ge_twelve s n hs hn
  have hFull : Navigation (4^K) :=
    gst_four_power_ontological_navigation_master K (by omega) (by omega)
  have hProj := canonical_tail_projection s (1 + 3*n) hs
    (by simpa [K] using hFull)
  exact hProj

end GSTPrefixOneOntologicalEscape
