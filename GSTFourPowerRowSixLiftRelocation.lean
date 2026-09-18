import GSTFourPowerPrefixKillingHappy

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace GSTFourPowerRowSixLiftRelocation

open GSTFourPowerDirectResidue
open GSTFourPowerExponentTritObstruction
open GSTFourPowerDirectExistence
open GSTFourPowerDirectHappyBridge

/-- Direct row-six lift.  A base exponent prefix `m`, exponent trit `a`, and higher
    tail `u` determine the two row-six digits without evaluating the enormous
    powers at the full exponent. -/
theorem row_six_physical_happy_of_lifted_prefix
    (m a u : Nat) (ha : a < 3)
    (h0 : (digit3 (4^m) 6 + a) % 3 = 2)
    (h1 : (digit3 (4^(m+1)) 6 + a) % 3 = 2) :
    let N := m + a * 3^5 + 3^6 * u
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  let N := m + a * 3^5 + 3^6 * u
  have hpair := pow4_shared_trit_pair 5 m a u ha
  have hrow : digit3 (4^N) 6 = 2 ∧ digit3 (4^(N+1)) 6 = 2 := by
    simpa [N] using And.intro (hpair.1.trans h0) (hpair.2.trans h1)
  have hCommon : CommonTwo N := ⟨6, by norm_num, hrow.1, hrow.2⟩
  exact commonTwo_to_physical_happy_row N hCommon

/-- The first residue at which direct `norm_num` on `4^r` exhausted the fresh
    compiler is handled structurally: `256 = 13 + 1*3^5`.  Only the small
    prefix powers `4^13` and `4^14` are evaluated. -/
theorem physical_happy_of_mod729_256
    (N : Nat) (hN : N % 729 = 256) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  have hm := Nat.mod_add_div N 729
  rw [hN] at hm
  have hdecomp : N = 13 + 1 * 3^5 + 3^6 * (N / 729) := by
    norm_num at hm ⊢
    omega
  rw [hdecomp]
  apply row_six_physical_happy_of_lifted_prefix 13 1 (N / 729) (by norm_num)
  · norm_num [digit3]
  · norm_num [digit3]

/-- Fresh physical relocation for the repaired row-six residue 256. -/
theorem four_power_happy_relocates_of_next_mod729_256
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 256) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_256 (K+1) hNext

#check row_six_physical_happy_of_lifted_prefix
#check physical_happy_of_mod729_256
#check four_power_happy_relocates_of_next_mod729_256
#print axioms row_six_physical_happy_of_lifted_prefix
#print axioms physical_happy_of_mod729_256
#print axioms four_power_happy_relocates_of_next_mod729_256

end GSTFourPowerRowSixLiftRelocation
