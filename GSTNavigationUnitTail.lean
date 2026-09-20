import GSTCanonicalTailStateIso
import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# LAW 1 of the seam dissection: the unit-tail base family

`Navigation (lteCoeff s)` holds for EVERY `s ≥ 2`:

* `s = 2` : happy row 4, carry 3 (finite check);
* `s = 3` : happy row 7, carry 0 (finite check);
* `s ≥ 4` : `lteCoeff s ≡ 178 mod 243` — stabilized by the cube-lift recursion
  built into the definition of `lteCoeff` — so row 4 has digit 2
  (`178 = 2·81 + 16`) and carry 0 (`178 mod 81 = 16 < 81/4`).

This is a happy-cell provider for the canonical family that the repo previously
lacked, and it is the base case of the seam descent (SEAM_DISSECTION.md, Law 5):
`canonicalTail s 1 = lteCoeff s` navigates, so every descent chain that bottoms
out at a unit tail terminates GREEN.
-/

namespace GSTNavigationUnitTail

open GSTCanonicalTailStateIso
open GSTCanonicalTailLTE

/-- The recursive definition is the exact cube lift:
`lteCoeff (s+1) = lteCoeff s + 3^(s+1)·(lteCoeff s)² + 3^(2s+1)·(lteCoeff s)³`. -/
theorem lteCoeff_step_eq (s : Nat) :
    lteCoeff (s+1) = lteCoeff s + 3^(s+1) * (lteCoeff s)^2 + 3^(2*s+1) * (lteCoeff s)^3 := by
  simp only [lteCoeff]

/-- Cube-lift stabilization: `lteCoeff (s+1) ≡ lteCoeff s (mod 3^(s+1))`. -/
theorem lteCoeff_step_mod (s : Nat) :
    lteCoeff (s+1) % 3^(s+1) = lteCoeff s % 3^(s+1) := by
  have hp : 3^(2*s+1) = 3^(s+1) * 3^s := by
    rw [show 2*s+1 = (s+1)+s by omega, Nat.pow_add]
  have h : lteCoeff (s+1) = lteCoeff s + 3^(s+1) * ((lteCoeff s)^2 + 3^s * (lteCoeff s)^3) := by
    rw [lteCoeff_step_eq s, hp]
    ring
  rw [h, Nat.add_mul_mod_self_left]

/-- Above scale four, every cube-lift step preserves the residue mod 243. -/
theorem lteCoeff_mod243_step (s : Nat) (hs : 4 ≤ s) :
    lteCoeff (s+1) % 243 = lteCoeff s % 243 := by
  have h243 : 243 ∣ 3^(s+1) := by
    refine ⟨3^(s-4), ?_⟩
    rw [show s + 1 = 5 + (s - 4) by omega, Nat.pow_add]
    try norm_num
  have h := lteCoeff_step_mod s
  have hl : lteCoeff (s+1) % 243 = (lteCoeff (s+1) % 3^(s+1)) % 243 :=
    (Nat.mod_mod_of_dvd (lteCoeff (s+1)) h243).symm
  have hr : lteCoeff s % 243 = (lteCoeff s % 3^(s+1)) % 243 :=
    (Nat.mod_mod_of_dvd (lteCoeff s) h243).symm
  rw [hl, hr, h]

/-- The stabilized pin: `lteCoeff s ≡ 178 mod 243` for every `s ≥ 4`. -/
theorem lteCoeff_mod243 (s : Nat) (hs : 4 ≤ s) : lteCoeff s % 243 = 178 := by
  have key : ∀ t : Nat, lteCoeff (4 + t) % 243 = 178 := by
    intro t
    induction t with
    | zero => exact (show lteCoeff 4 % 243 = 178 by decide)
    | succ t ih =>
      have h1 : 4 + (t + 1) = (4 + t) + 1 := by omega
      rw [h1]
      exact (lteCoeff_mod243_step (4 + t) (by omega)).trans ih
  rw [show s = 4 + (s - 4) by omega]
  exact key (s - 4)

/-- The unit-tail happy pin at row 4 for every `s ≥ 4`: digit two, carry zero. -/
theorem lteCoeff_happy_four_ge (s : Nat) (hs : 4 ≤ s) :
    HappyCell (carry4 (lteCoeff s) 4) (digit3 (lteCoeff s) 4) := by
  have h81 : (3:Nat)^4 = 81 := by decide
  have h := lteCoeff_mod243 s hs
  have hd := Nat.div_add_mod (lteCoeff s) 243
  rw [h] at hd
  have hq : lteCoeff s = 243 * (lteCoeff s / 243) + 178 := hd.symm
  refine ⟨?_, Or.inl ?_⟩
  · unfold digit3
    rw [h81, hq]
    omega
  · unfold carry4
    rw [h81, hq]
    omega

/-- The finite base `s = 2`: happy row 4, carry 3. -/
theorem lteCoeff_happy_two : HappyCell (carry4 (lteCoeff 2) 4) (digit3 (lteCoeff 2) 4) :=
  ⟨by decide, Or.inr (by decide)⟩

/-- The finite base `s = 3`: happy row 7, carry 0. -/
theorem lteCoeff_happy_three : HappyCell (carry4 (lteCoeff 3) 7) (digit3 (lteCoeff 3) 7) :=
  ⟨by decide, Or.inl (by decide)⟩

/-- **LAW 1 — the unit-tail base family.** Every unit tail navigates:
`Navigation (lteCoeff s)` for all `s ≥ 2`. -/
theorem navigation_unit_tail (s : Nat) (hs : 2 ≤ s) : Navigation (lteCoeff s) := by
  rcases (show s = 2 ∨ s = 3 ∨ 4 ≤ s by omega) with rfl | rfl | h4
  · exact ⟨4, lteCoeff_happy_two⟩
  · exact ⟨7, lteCoeff_happy_three⟩
  · exact ⟨4, lteCoeff_happy_four_ge s h4⟩

end GSTNavigationUnitTail
