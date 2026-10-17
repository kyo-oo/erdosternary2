import Mathlib

/-!
# GST Graph V2 — canonical experimental kernel

This file is deliberately isolated from `ErdosTernary2.lean`.
It rebuilds the exact finite arithmetic core of the recent Sol V2 tree as one
computed graph object, without importing the historical snapshot directory.

It proves only structural identities that were already established in the
scratch tree.  The final phase-crossing statement is represented as a `Prop`
target, not asserted as a theorem.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Experiment

/-- Ternary input digit at row `p`. -/
def digit (R p : Nat) : Nat := R / 3^p % 3

/-- Ordinary x4 GST carry at row `p`. -/
def carry (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

/-- One x4 carry transition. -/
def stepCarry (C d : Nat) : Nat := (C + 4*d) / 3

/-- Carry of a general affine realization `z + A*T`. -/
def affineCarry (A z T p : Nat) : Nat :=
  (z + A * (T % 3^p)) / 3^p

/-- Seeded Happy/SURVIVE cell. -/
def SeededHappy (D X q : Nat) : Prop :=
  digit X q = 2 ∧
    (affineCarry 4 D X q = 0 ∨ affineCarry 4 D X q = 3)

/-- Complete seeded bad language. -/
def SeededBadTrace (D X : Nat) : Prop :=
  ∀ q, ¬ SeededHappy D X q

/-- Exact carry recurrence, including row zero. -/
theorem carry_forward_exact (R p : Nat) :
    carry R (p+1) = stepCarry (carry R p) (digit R p) := by
  simp only [carry, digit, stepCarry, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R % (3^p * 3) = R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show 4 * (3^p * (R / 3^p % 3)) =
      3^p * (4 * (R / 3^p % 3)) by ac_rfl]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

/-- Ternary digits reindex exactly through a cut. -/
theorem digit_shift (X q j : Nat) :
    digit X (q+j) = digit (X / 3^q) j := by
  simp only [digit]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- Seeded affine carries compose exactly through a cut. -/
theorem seeded_carry_semigroup (D X q j : Nat) :
    affineCarry 4 D X (q+j) =
      affineCarry 4 (affineCarry 4 D X q) (X / 3^q) j := by
  simp only [affineCarry]
  rw [Nat.pow_add, Nat.mod_mul]
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hshape : D + 4 * (X % 3^q + 3^q * (X / 3^q % 3^j)) =
      (D + 4 * (X % 3^q)) + 3^q * (4 * (X / 3^q % 3^j)) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [hshape, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hqpos]

/-- Exact quotient decomposition of an affine realization. -/
theorem affine_tail_div_decomposition (z A T q : Nat) :
    (z + A*T) / 3^q = affineCarry A z T q + A*(T / 3^q) := by
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hdiv : T = 3^q * (T / 3^q) + T % 3^q :=
    (Nat.div_add_mod T (3^q)).symm
  rw [hdiv, Nat.mul_add]
  rw [show A * (3^q * (T / 3^q)) =
      3^q * (A * (T / 3^q)) by ac_rfl]
  rw [show z + (3^q * (A * (T / 3^q)) + A * (T % 3^q)) =
      (z + A * (T % 3^q)) + 3^q * (A * (T / 3^q)) by ac_rfl]
  rw [Nat.add_mul_div_left _ _ hqpos, ← hdiv]
  simp [affineCarry]

/-- The central V2 conservation equation.  One integer is read simultaneously
as parent-seed/low-affine data and as latent-remainder/child-carry data. -/
theorem shared_information_equation (A z T q : Nat) :
    affineCarry A (1 + 4*z) (4*T) q + A * carry T q =
      affineCarry 4 1 (z + A*T) q + 4 * affineCarry A z T q := by
  have hx := affine_tail_div_decomposition z A T q
  have hy := affine_tail_div_decomposition (1 + 4*z) A (4*T) q
  have hp := affine_tail_div_decomposition 1 4 (z + A*T) q
  have ht := affine_tail_div_decomposition 0 4 T q
  have ht' : (4*T) / 3^q = carry T q + 4*(T / 3^q) := by
    simpa [carry, affineCarry] using ht
  have hnum : (1 + 4*z) + A*(4*T) = 1 + 4*(z + A*T) := by
    ring
  have hfull :
      ((1 + 4*z) + A*(4*T)) / 3^q =
        (1 + 4*(z + A*T)) / 3^q := by rw [hnum]
  rw [hy, hp, hx, ht'] at hfull
  ring_nf at hfull ⊢
  omega

/-- Any affine carry remains inside the multiplier interval when its seed does. -/
theorem affine_carry_lt_multiplier
    (A z T q : Nat) (hA : 0 < A) (hz : z < A) :
    affineCarry A z T q < A := by
  unfold affineCarry
  have hM : 0 < 3^q := Nat.pow_pos (by decide)
  have hr : T % 3^q < 3^q := Nat.mod_lt T hM
  have hnum : z + A * (T % 3^q) < 3^q * A := by
    calc
      z + A * (T % 3^q) < A + A * (T % 3^q) :=
        Nat.add_lt_add_right hz _
      _ = A * ((T % 3^q) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        ac_rfl
      _ ≤ A * 3^q := Nat.mul_le_mul_left A (Nat.succ_le_of_lt hr)
      _ = 3^q * A := by ac_rfl
  exact Nat.div_lt_of_lt_mul hnum

inductive Space
  | null
  | altMinus
  | gstPlus
  deriving Repr, DecidableEq

/-- Physical carry-space label. -/
def spaceOfCarry (C : Nat) : Space :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

inductive Event
  | create
  | destroy
  | survive
  | neither
  deriving Repr, DecidableEq

/-- Output ternary digit of one x4 cell. -/
def outputDigit (C d : Nat) : Nat := (C + 4*d) % 3

/-- CREATE/DESTROY/SURVIVE/NEITHER event classification. -/
def eventOf (C d : Nat) : Event :=
  let e := outputDigit C d
  if d = 2 then
    if e = 2 then .survive else .destroy
  else
    if e = 2 then .create else .neither

/-- For legal GST carries/digits, SURVIVE is exactly Happy. -/
theorem survive_iff_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    eventOf C d = .survive ↔ d = 2 ∧ (C = 0 ∨ C = 3) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    decide

/-- First microscopic x2 mass of one physical x4 cell. -/
def firstMicroMass (C d : Nat) : Nat := C / 2 + 2*d

def firstMicroOutput (C d : Nat) : Nat := firstMicroMass C d % 3

/-- Second microscopic x2 mass of the same physical x4 cell. -/
def secondMicroMass (C d : Nat) : Nat := C % 2 + 2*firstMicroOutput C d

/-- The ordered physical six-state pair. -/
def microPair (C d : Nat) : Nat × Nat :=
  (firstMicroMass C d, secondMicroMass C d)

/-- Exact six-state gate dictionary: NULL is `(4,2)` and GST+ is `(5,5)`. -/
theorem micro_pair_happy_iff
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (d = 2 ∧ (C = 0 ∨ C = 3)) ↔
      (microPair C d = (4,2) ∨ microPair C d = (5,5)) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [microPair, firstMicroMass, secondMicroMass, firstMicroOutput]

/-- A complete V2 frame at one ternary row.  Every field is computed from the
same canonical affine object rather than supplied independently. -/
structure Frame where
  row : Nat
  parentSeedCarry : Nat
  parentDigit : Nat
  lowAffineCarry : Nat
  childCarry : Nat
  childDigit : Nat
  latentCarry : Nat
  sharedCarrier : Nat
  childMicroPair : Nat × Nat
  deriving Repr, DecidableEq

/-- Computed graph frame for `H = z + A*T`. -/
def frame (A z T q : Nat) : Frame :=
  let H := z + A*T
  let p := affineCarry 4 1 H q
  let a0 := affineCarry A z T q
  let C := carry T q
  let d := digit T q
  let W := affineCarry A (1 + 4*z) (4*T) q
  {
    row := q
    parentSeedCarry := p
    parentDigit := digit H q
    lowAffineCarry := a0
    childCarry := C
    childDigit := d
    latentCarry := W
    sharedCarrier := p + 4*a0
    childMicroPair := microPair C d
  }

/-- The two coordinate readings of the V2 frame are exactly the same integer. -/
theorem frame_shared_conservation (A z T q : Nat) :
    (frame A z T q).latentCarry + A * (frame A z T q).childCarry =
      (frame A z T q).sharedCarrier := by
  simpa [frame] using shared_information_equation A z T q

/-- Under the canonical offset bound, child carry is the base-A quotient of the
single shared carrier. -/
theorem frame_childCarry_is_quotient
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A) :
    (frame A z T q).childCarry = (frame A z T q).sharedCarrier / A := by
  have hEq := frame_shared_conservation A z T q
  have hW : (frame A z T q).latentCarry < A := by
    simpa [frame] using
      affine_carry_lt_multiplier A (1 + 4*z) (4*T) q hA hz1
  have hshape :
      (frame A z T q).sharedCarrier =
        A * (frame A z T q).childCarry + (frame A z T q).latentCarry := by
    omega
  rw [hshape]
  exact (Nat.mul_add_div A (frame A z T q).childCarry
    (frame A z T q).latentCarry).trans (by
      rw [Nat.div_eq_of_lt hW]
      simp [hA])

/-- Under the same bound, latent information is the base-A remainder. -/
theorem frame_latentCarry_is_remainder
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A) :
    (frame A z T q).latentCarry = (frame A z T q).sharedCarrier % A := by
  have hEq := frame_shared_conservation A z T q
  have hW : (frame A z T q).latentCarry < A := by
    simpa [frame] using
      affine_carry_lt_multiplier A (1 + 4*z) (4*T) q hA hz1
  have hshape :
      (frame A z T q).sharedCarrier =
        A * (frame A z T q).childCarry + (frame A z T q).latentCarry := by
    omega
  rw [hshape, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hW, hA]

/-- A localized child Happy gate remains a real physical six-state gate inside
its computed V2 frame. -/
theorem frame_child_happy_iff_micro_pair
    (A z T q : Nat) :
    (digit T q = 2 ∧ (carry T q = 0 ∨ carry T q = 3)) ↔
      ((frame A z T q).childMicroPair = (4,2) ∨
       (frame A z T q).childMicroPair = (5,5)) := by
  have hC : carry T q < 4 := by
    have h := affine_carry_lt_multiplier 4 0 T q (by decide) (by decide)
    simpa [carry, affineCarry] using h
  have hd : digit T q < 3 := by
    unfold digit
    exact Nat.mod_lt _ (by decide)
  simpa [frame] using micro_pair_happy_iff (carry T q) (digit T q) hC hd

/-- Exact phase-two boundary object from the three-phase Sol spacetime picture. -/
def phaseTwoEnergy (s H : Nat) : Nat :=
  1 + 2*3^(s+1) + 3^(s+2)*H

/-- Phase two has an unconditional physical Happy gate at its phase boundary. -/
theorem phase_two_boundary_happy
    (s H : Nat) (hs : 1 ≤ s) :
    digit (phaseTwoEnergy s H) (s+1) = 2 ∧
      carry (phaseTwoEnergy s H) (s+1) = 0 := by
  let D := 3^(s+1)
  have hD9 : 9 ≤ D := by
    dsimp [D]
    rw [show (9:Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hDpos : 0 < D := by omega
  have hpow : 3^(s+2) = 3*D := by
    dsimp [D]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hshape :
      phaseTwoEnergy s H = 1 + D * (2 + 3*H) := by
    unfold phaseTwoEnergy
    rw [show 3^(s+1) = D by rfl, hpow]
    ring
  rw [hshape]
  constructor
  · have htail : (1 + D * (2 + 3*H)) / D = 2 + 3*H := by
      rw [Nat.add_mul_div_left 1 (2+3*H) hDpos]
      rw [Nat.div_eq_of_lt (by omega : 1 < D)]
      simp
    unfold digit
    rw [show 3^(s+1) = D by rfl, htail]
    omega
  · unfold carry
    rw [show 3^(s+1) = D by rfl]
    have hmod : (1 + D * (2 + 3*H)) % D = 1 := by
      rw [Nat.add_mod, Nat.mul_mod]
      simp [Nat.mod_eq_of_lt (by omega : 1 < D)]
    rw [hmod]
    exact Nat.div_eq_of_lt (by omega : 4 < D)

/-- The exact experiment target.  This is intentionally a proposition, not a
claimed theorem: a phase-zero/child gate must eventually produce a phase-one
seed-one gate on the canonical pure-power orbit. -/
def CanonicalPhaseCrossingTarget (T H : Nat) : Prop :=
  (∃ q, SeededHappy 0 T q) → ∃ q, SeededHappy 1 H q

end GSTGraphV2Experiment
