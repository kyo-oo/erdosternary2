import GSTFourPowerAffineSixthTrit606_613

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTrit617_619

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod729_eq_440_of_exponent_617
    (N : Nat) (hN : N % 729 = 617) :
    affineOrbit N % 729 = 440 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 617).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `22` forces `1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_22_617
    (N : Nat) (hAmod : affineOrbit N % 729 = 440) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixOneSeven
    (N : Nat) (hN : N % 729 = 617) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_22_617 N
    (affineOrbit_mod729_eq_440_of_exponent_617 N hN)

theorem physical_happy_of_mod729_sixOneSeven
    (N : Nat) (hN : N % 729 = 617) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixOneSeven N hN)

theorem four_power_happy_propagates_of_next_mod729_sixOneSeven
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 617) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixOneSeven (K+1) hNext

private theorem affineOrbit_mod729_eq_303_of_exponent_618
    (N : Nat) (hN : N % 729 = 618) :
    affineOrbit N % 729 = 303 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 618).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `02` forces `1 -> 0`, then trit `2` kills state `0`. -/
private theorem commonTwo_of_mod729_pattern_02_618
    (N : Nat) (hAmod : affineOrbit N % 729 = 303) : CommonTwo N := by
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

theorem commonTwo_of_mod729_sixOneEight
    (N : Nat) (hN : N % 729 = 618) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_02_618 N
    (affineOrbit_mod729_eq_303_of_exponent_618 N hN)

theorem physical_happy_of_mod729_sixOneEight
    (N : Nat) (hN : N % 729 = 618) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixOneEight N hN)

theorem four_power_happy_propagates_of_next_mod729_sixOneEight
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 618) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixOneEight (K+1) hNext

private theorem affineOrbit_mod729_eq_484_of_exponent_619
    (N : Nat) (hN : N % 729 = 619) :
    affineOrbit N % 729 = 484 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 619).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Prefix `122` forces `1 -> 1 -> 3`, then trit `2` kills state `3`. -/
private theorem commonTwo_of_mod729_pattern_122_619
    (N : Nat) (hAmod : affineOrbit N % 729 = 484) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 1 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad1
    simpa using hbad1
  rw [badChannel_three_iff, hd2] at hbad2
  simpa using hbad2

theorem commonTwo_of_mod729_sixOneNine
    (N : Nat) (hN : N % 729 = 619) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_122_619 N
    (affineOrbit_mod729_eq_484_of_exponent_619 N hN)

theorem physical_happy_of_mod729_sixOneNine
    (N : Nat) (hN : N % 729 = 619) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_sixOneNine N hN)

theorem four_power_happy_propagates_of_next_mod729_sixOneNine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 619) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_sixOneNine (K+1) hNext

end GSTFourPowerAffineSixthTrit617_619
