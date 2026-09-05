import GSTFourPowerAffineSixthTrit589_592

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit599_603

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_287_of_exponent_599
    (N : Nat) (hN : N % 729 = 599) :
    affineOrbit N % 729 = 287 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 599).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_599
    (N : Nat) (hAmod : affineOrbit N % 729 = 287) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  rw [badChannel_three_iff, hd1] at hbad1
  simpa using hbad1

theorem commonTwo_of_mod729_fiveNineNine
    (N : Nat) (hN : N % 729 = 599) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_599 N
    (affineOrbit_mod729_eq_287_of_exponent_599 N hN)

theorem physical_happy_of_mod729_fiveNineNine
    (N : Nat) (hN : N % 729 = 599) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fiveNineNine N hN)

theorem four_power_happy_propagates_of_next_mod729_fiveNineNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 599) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fiveNineNine (K+1) hNext

private theorem affineOrbit_mod729_eq_420_of_exponent_600
    (N : Nat) (hN : N % 729 = 600) :
    affineOrbit N % 729 = 420 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 600).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_600
    (N : Nat) (hAmod : affineOrbit N % 729 = 420) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  rw [badChannel_zero_iff, hd1] at hbad1
  simpa using hbad1

theorem commonTwo_of_mod729_sixZeroZero
    (N : Nat) (hN : N % 729 = 600) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_600 N
    (affineOrbit_mod729_eq_420_of_exponent_600 N hN)

theorem physical_happy_of_mod729_sixZeroZero
    (N : Nat) (hN : N % 729 = 600) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixZeroZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sixZeroZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 600) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixZeroZero (K+1) hNext

private theorem affineOrbit_mod729_eq_223_of_exponent_601
    (N : Nat) (hN : N % 729 = 601) :
    affineOrbit N % 729 = 223 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 601).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `12022` forces `1 -> 1 -> 3 -> 1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_12022_601
    (N : Nat) (hAmod : affineOrbit N % 729 = 223) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixZeroOne
    (N : Nat) (hN : N % 729 = 601) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_12022_601 N
    (affineOrbit_mod729_eq_223_of_exponent_601 N hN)

theorem physical_happy_of_mod729_sixZeroOne
    (N : Nat) (hN : N % 729 = 601) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixZeroOne N hN)

theorem four_power_happy_propagates_of_next_mod729_sixZeroOne
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 601) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixZeroOne (K+1) hNext

private theorem affineOrbit_mod729_eq_164_of_exponent_602
    (N : Nat) (hN : N % 729 = 602) :
    affineOrbit N % 729 = 164 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 602).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `20002` forces `1 -> 3 -> 1 -> 0 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_20002_602
    (N : Nat) (hAmod : affineOrbit N % 729 = 164) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 2 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 3 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 1 (tail3 (tail3 A)) := by
    rw [badChannel_three_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_one_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixZeroTwo
    (N : Nat) (hN : N % 729 = 602) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_20002_602 N
    (affineOrbit_mod729_eq_164_of_exponent_602 N hN)

theorem physical_happy_of_mod729_sixZeroTwo
    (N : Nat) (hN : N % 729 = 602) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixZeroTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sixZeroTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 602) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixZeroTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_657_of_exponent_603
    (N : Nat) (hN : N % 729 = 603) :
    affineOrbit N % 729 = 657 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 603).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `00102` forces `1 -> 0 -> 0 -> 1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_00102_603
    (N : Nat) (hAmod : affineOrbit N % 729 = 657) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by
    unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 1 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_one_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_zero_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixZeroThree
    (N : Nat) (hN : N % 729 = 603) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_00102_603 N
    (affineOrbit_mod729_eq_657_of_exponent_603 N hN)

theorem physical_happy_of_mod729_sixZeroThree
    (N : Nat) (hN : N % 729 = 603) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixZeroThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixZeroThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 603) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixZeroThree (K+1) hNext

#check physical_happy_of_mod729_fiveNineNine
#check physical_happy_of_mod729_sixZeroZero
#check physical_happy_of_mod729_sixZeroOne
#check physical_happy_of_mod729_sixZeroTwo
#check physical_happy_of_mod729_sixZeroThree
#print axioms physical_happy_of_mod729_fiveNineNine
#print axioms physical_happy_of_mod729_sixZeroZero
#print axioms physical_happy_of_mod729_sixZeroOne
#print axioms physical_happy_of_mod729_sixZeroTwo
#print axioms physical_happy_of_mod729_sixZeroThree

end GSTFourPowerAffineSixthTrit599_603
