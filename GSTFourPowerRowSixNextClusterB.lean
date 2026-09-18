import GSTFourPowerRowSixLiftRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace GSTFourPowerRowSixNextClusterB

open GSTFourPowerDirectResidue
open GSTFourPowerRowSixLiftRelocation

/-- Next structural row-six overlap: `288 = 45 + 1*3^5`. -/
theorem physical_happy_of_mod729_288
    (N : Nat) (hN : N % 729 = 288) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 45 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- Consecutive structural row-six overlap: `289 = 46 + 1*3^5`. -/
theorem physical_happy_of_mod729_289
    (N : Nat) (hN : N % 729 = 289) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 46 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- Next separated structural row-six overlap: `292 = 49 + 1*3^5`. -/
theorem physical_happy_of_mod729_292
    (N : Nat) (hN : N % 729 = 292) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 49 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- Direct physical relocation into target residue 288 modulo 729. -/
theorem four_power_happy_relocates_of_next_mod729_288
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 288) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_288 (K+1) hNext

/-- Direct physical relocation into target residue 289 modulo 729. -/
theorem four_power_happy_relocates_of_next_mod729_289
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 289) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_289 (K+1) hNext

/-- Direct physical relocation into target residue 292 modulo 729. -/
theorem four_power_happy_relocates_of_next_mod729_292
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 292) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_292 (K+1) hNext

#check physical_happy_of_mod729_288
#check physical_happy_of_mod729_289
#check physical_happy_of_mod729_292
#print axioms physical_happy_of_mod729_288
#print axioms physical_happy_of_mod729_289
#print axioms physical_happy_of_mod729_292
#print axioms four_power_happy_relocates_of_next_mod729_288
#print axioms four_power_happy_relocates_of_next_mod729_289
#print axioms four_power_happy_relocates_of_next_mod729_292

end GSTFourPowerRowSixNextClusterB
