import GSTFourPowerAffineSixthTrit599_603

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit606_613

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_242_of_exponent_608
    (N : Nat) (hN : N % 729 = 608) :
    affineOrbit N % 729 = 242 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 608).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_608
    (N : Nat) (hAmod : affineOrbit N % 729 = 242) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixZeroEight
    (N : Nat) (hN : N % 729 = 608) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_608 N
    (affineOrbit_mod729_eq_242_of_exponent_608 N hN)

theorem physical_happy_of_mod729_sixZeroEight
    (N : Nat) (hN : N % 729 = 608) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixZeroEight N hN)

theorem four_power_happy_propagates_of_next_mod729_sixZeroEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 608) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixZeroEight (K+1) hNext

private theorem affineOrbit_mod729_eq_240_of_exponent_609
    (N : Nat) (hN : N % 729 = 609) :
    affineOrbit N % 729 = 240 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 609).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_609
    (N : Nat) (hAmod : affineOrbit N % 729 = 240) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixZeroNine
    (N : Nat) (hN : N % 729 = 609) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_609 N
    (affineOrbit_mod729_eq_240_of_exponent_609 N hN)

theorem physical_happy_of_mod729_sixZeroNine
    (N : Nat) (hN : N % 729 = 609) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixZeroNine N hN)

theorem four_power_happy_propagates_of_next_mod729_sixZeroNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 609) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixZeroNine (K+1) hNext

private theorem affineOrbit_mod729_eq_232_of_exponent_610
    (N : Nat) (hN : N % 729 = 610) :
    affineOrbit N % 729 = 232 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 610).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `12122` forces `1 -> 1 -> 3 -> 2 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_12122_610
    (N : Nat) (hAmod : affineOrbit N % 729 = 232) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 1 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 2 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_three_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 3 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_two_iff, hd3] at hbad3
    simpa using hbad3
  rw [badChannel_three_iff, hd4] at hbad4
  simpa using hbad4

theorem commonTwo_of_mod729_sixOneZero
    (N : Nat) (hN : N % 729 = 610) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_12122_610 N
    (affineOrbit_mod729_eq_232_of_exponent_610 N hN)

theorem physical_happy_of_mod729_sixOneZero
    (N : Nat) (hN : N % 729 = 610) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixOneZero N hN)

theorem four_power_happy_propagates_of_next_mod729_sixOneZero
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 610) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixOneZero (K+1) hNext

private theorem affineOrbit_mod729_eq_72_of_exponent_612
    (N : Nat) (hN : N % 729 = 612) :
    affineOrbit N % 729 = 72 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 612).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `002` forces `1 -> 0 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_002_612
    (N : Nat) (hAmod : affineOrbit N % 729 = 72) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  rw [badChannel_zero_iff, hd2] at hbad2
  simpa using hbad2

theorem commonTwo_of_mod729_sixOneTwo
    (N : Nat) (hN : N % 729 = 612) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_002_612 N
    (affineOrbit_mod729_eq_72_of_exponent_612 N hN)

theorem physical_happy_of_mod729_sixOneTwo
    (N : Nat) (hN : N % 729 = 612) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixOneTwo N hN)

theorem four_power_happy_propagates_of_next_mod729_sixOneTwo
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 612) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixOneTwo (K+1) hNext

private theorem affineOrbit_mod729_eq_289_of_exponent_613
    (N : Nat) (hN : N % 729 = 613) :
    affineOrbit N % 729 = 289 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 613).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `102` forces `1 -> 1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_102_613
    (N : Nat) (hAmod : affineOrbit N % 729 = 289) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  rw [badChannel_zero_iff, hd2] at hbad2
  simpa using hbad2

theorem commonTwo_of_mod729_sixOneThree
    (N : Nat) (hN : N % 729 = 613) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_102_613 N
    (affineOrbit_mod729_eq_289_of_exponent_613 N hN)

theorem physical_happy_of_mod729_sixOneThree
    (N : Nat) (hN : N % 729 = 613) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixOneThree N hN)

theorem four_power_happy_propagates_of_next_mod729_sixOneThree
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 613) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixOneThree (K+1) hNext

end GSTFourPowerAffineSixthTrit606_613
