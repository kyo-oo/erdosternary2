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

/-- Structural row-six constructor for a concrete residue represented as
    `m + a*3^5` modulo `3^6`.  This keeps all full-exponent powers out of
    normalization and exposes only the small prefix powers. -/
theorem physical_happy_of_mod729_lifted_prefix
    (N m a : Nat) (ha : a < 3)
    (hN : N % 729 = m + a * 3^5)
    (h0 : (digit3 (4^m) 6 + a) % 3 = 2)
    (h1 : (digit3 (4^(m+1)) 6 + a) % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  have hm := Nat.mod_add_div N 729
  rw [hN] at hm
  have hdecomp : N = m + a * 3^5 + 3^6 * (N / 729) := by
    norm_num at hm ⊢
    omega
  rw [hdecomp]
  exact row_six_physical_happy_of_lifted_prefix m a (N / 729) ha h0 h1

/-- The first residue at which direct `norm_num` on `4^r` exhausted the fresh
    compiler is handled structurally: `256 = 13 + 1*3^5`. -/
theorem physical_happy_of_mod729_256
    (N : Nat) (hN : N % 729 = 256) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 13 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- The immediately following row-six overlap, `257 = 14 + 1*3^5`, is
    constructed by the same structural lift. -/
theorem physical_happy_of_mod729_257
    (N : Nat) (hN : N % 729 = 257) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 14 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
  · norm_num [digit3]
  · norm_num [digit3]

/-- And `258 = 15 + 1*3^5`; this advances the repaired production route
    without reintroducing giant-power normalization. -/
theorem physical_happy_of_mod729_258
    (N : Nat) (hN : N % 729 = 258) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  apply physical_happy_of_mod729_lifted_prefix N 15 1 (by norm_num)
  · norm_num at hN ⊢
    exact hN
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

/-- Fresh physical relocation for target residue 257. -/
theorem four_power_happy_relocates_of_next_mod729_257
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 257) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_257 (K+1) hNext

/-- Fresh physical relocation for target residue 258. -/
theorem four_power_happy_relocates_of_next_mod729_258
    (K sourceRow : Nat) (_hsourceRow : 1 ≤ sourceRow)
    (_hSource :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) sourceRow)
        (GSTCanonicalTailStateIso.digit3 (4^K) sourceRow))
    (hNext : (K+1) % 729 = 258) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_258 (K+1) hNext

#check row_six_physical_happy_of_lifted_prefix
#check physical_happy_of_mod729_lifted_prefix
#check physical_happy_of_mod729_256
#check physical_happy_of_mod729_257
#check physical_happy_of_mod729_258
#check four_power_happy_relocates_of_next_mod729_256
#check four_power_happy_relocates_of_next_mod729_257
#check four_power_happy_relocates_of_next_mod729_258
#print axioms row_six_physical_happy_of_lifted_prefix
#print axioms physical_happy_of_mod729_lifted_prefix
#print axioms physical_happy_of_mod729_256
#print axioms physical_happy_of_mod729_257
#print axioms physical_happy_of_mod729_258
#print axioms four_power_happy_relocates_of_next_mod729_256
#print axioms four_power_happy_relocates_of_next_mod729_257
#print axioms four_power_happy_relocates_of_next_mod729_258

end GSTFourPowerRowSixLiftRelocation
