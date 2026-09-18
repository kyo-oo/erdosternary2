import GSTFourPowerRowSixLiftRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace GSTFourPowerRowSixNextCluster

open GSTFourPowerDirectResidue
open GSTFourPowerRowSixLiftRelocation

/-- The next row-six overlap after 258: `269 = 26 + 1*3^5`. -/
theorem physical_happy_of_mod729_269
    (N : Nat) (hN : N % 729 = 269) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 26 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- Consecutive row-six overlap `270 = 27 + 1*3^5`. -/
theorem physical_happy_of_mod729_270
    (N : Nat) (hN : N % 729 = 270) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 27 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- Consecutive row-six overlap `271 = 28 + 1*3^5`. -/
theorem physical_happy_of_mod729_271
    (N : Nat) (hN : N % 729 = 271) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 28 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- Direct physical relocation into the 269 row-six target class. -/
theorem four_power_happy_relocates_of_next_mod729_269
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 269) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_269 (K+1) hNext

/-- Direct physical relocation into the 270 row-six target class. -/
theorem four_power_happy_relocates_of_next_mod729_270
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 270) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_270 (K+1) hNext

/-- Direct physical relocation into the 271 row-six target class. -/
theorem four_power_happy_relocates_of_next_mod729_271
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 271) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_271 (K+1) hNext

#check physical_happy_of_mod729_269
#check physical_happy_of_mod729_270
#check physical_happy_of_mod729_271
#check four_power_happy_relocates_of_next_mod729_269
#check four_power_happy_relocates_of_next_mod729_270
#check four_power_happy_relocates_of_next_mod729_271
#print axioms physical_happy_of_mod729_269
#print axioms physical_happy_of_mod729_270
#print axioms physical_happy_of_mod729_271
#print axioms four_power_happy_relocates_of_next_mod729_269
#print axioms four_power_happy_relocates_of_next_mod729_270
#print axioms four_power_happy_relocates_of_next_mod729_271

end GSTFourPowerRowSixNextCluster
