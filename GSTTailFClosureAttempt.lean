import GSTTailFFourthDimension

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTTailFClosureAttempt

open GSTCanonicalSevenAxisBridge
open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-- A TailF observer dodge at a legal tower level really means that the
corresponding power digit is not two. -/
theorem observer_dodge_digit_ne_two
    (S core k : Nat)
    (hk3 : 3 ≤ k) (hkS : k ≤ S + 1)
    (hD : ∀ q : Nat, 3 ≤ q → q ≤ S + 1 →
      (omegaCutWord S 1 * core) % 3^q < 2 * 3^(q-1)) :
    digit3 (4^(3^S * core)) (S + k) ≠ 2 := by
  have hobs := omega_observed_digit S core k (by omega) hkS
  have hd := hD k hk3 hkS
  rw [hobs]
  have hp : 0 < 3^(k-1) := Nat.pow_pos (by decide)
  have hlt : ((omegaCutWord S 1 * core) % 3^k) / 3^(k-1) < 2 := by
    exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hd)
  omega

/-- The child sheet's maximum observer dodge forbids a parent sheet-gate
trit one. -/
theorem child_observer_forces_parent_gate_ne_one
    (s core : Nat) (hs : 1 ≤ s) (hcore : core % 3 = 1)
    (hD : ∀ q : Nat, 3 ≤ q → q ≤ (s+1) + 1 →
      (omegaCutWord (s+1) 1 * core) % 3^q < 2 * 3^(q-1)) :
    digit3 (4^(3^s * core)) (2*s+2) ≠ 1 := by
  intro hparent
  have hchild : digit3 (4^(3^(s+1) * core)) (2*s+3) = 2 :=
    omega_tripling_gate s core hs hcore hparent
  have hnot := observer_dodge_digit_ne_two (s+1) core (s+2)
    (by omega) (by omega) hD
  have hidx : (s+1) + (s+2) = 2*s+3 := by omega
  rw [hidx] at hnot
  exact hnot hchild

/-- One TailF tower observer at sheet `S` projects backwards to every
earlier parent gate. -/
theorem tailF_observer_backward_pressure
    (S core r : Nat)
    (hr1 : 1 ≤ r) (hrS : r + 1 ≤ S)
    (hcore : core % 3 = 1)
    (hD : ∀ q : Nat, 3 ≤ q → q ≤ S + 1 →
      (omegaCutWord S 1 * core) % 3^q < 2 * 3^(q-1)) :
    digit3 (4^(3^r * core)) (2*r+2) ≠ 1 := by
  intro hparent
  have hchild : digit3 (4^(3^(r+1) * core)) (2*r+3) = 2 :=
    omega_tripling_gate r core hr1 hcore hparent
  have hcur := hD (r+2) (by omega) (by omega)
  have hchain := omega_tower_word_mod_chain core (r+2) S (by omega)
  have hprim :
      (omegaCutWord (r+1) 1 * core) % 3^(r+2) < 2 * 3^((r+2)-1) := by
    have hcur' := hcur
    rw [hchain] at hcur'
    simpa using hcur'
  have hobs := omega_observed_digit (r+1) core (r+2) (by omega) (by omega)
  have hp : 0 < 3^((r+2)-1) := Nat.pow_pos (by decide)
  have hlt : ((omegaCutWord (r+1) 1 * core) % 3^(r+2)) /
      3^((r+2)-1) < 2 := by
    exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hprim)
  have hnot : digit3 (4^(3^(r+1) * core)) ((r+1)+(r+2)) ≠ 2 := by
    rw [hobs]
    omega
  have hidx : (r+1)+(r+2) = 2*r+3 := by omega
  rw [hidx] at hnot
  exact hnot hchild

/-- Under a surviving observer at sheet `S`, every earlier sheet window is
forced into a binary state: TOP (it fires on that lower sheet) or BOTTOM.
The MIDDLE state would escalate a digit two into sheet `S`, contradicting
that observer. -/
theorem tailF_lower_sheet_top_or_bottom
    (S core r : Nat)
    (hr1 : 1 ≤ r) (hrS : r + 1 ≤ S)
    (hcore : core % 3 = 1)
    (hD : ∀ q : Nat, 3 ≤ q → q ≤ S + 1 →
      (omegaCutWord S 1 * core) % 3^q < 2 * 3^(q-1)) :
    2 * 3^(r+1) ≤ (omegaCutWord r core) % 3^(r+2) ∨
      (omegaCutWord r core) % 3^(r+2) < 3^(r+1) := by
  rcases omega_sheet_window_dichotomy r core hr1 (Or.inl hcore) with
    htop | hbottom | hmiddle
  · exact Or.inl htop.1
  · exact Or.inr hbottom
  · exfalso
    have htwo := hmiddle.2.2 S hrS
    have hnot := observer_dodge_digit_ne_two S core (r+2)
      (by omega) (by omega) hD
    exact hnot htwo

#print axioms observer_dodge_digit_ne_two
#print axioms child_observer_forces_parent_gate_ne_one
#print axioms tailF_observer_backward_pressure
#print axioms tailF_lower_sheet_top_or_bottom

end GSTTailFClosureAttempt
