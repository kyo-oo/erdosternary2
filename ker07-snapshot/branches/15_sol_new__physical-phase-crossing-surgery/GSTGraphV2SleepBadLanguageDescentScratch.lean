import GSTGraphV2SleepEquationLabScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# BIG1-free bad-language collapse for the handwritten S/U operator

This is the finite-language side of the two-axis descent suggested by the full
sleep operator.  A complete bad suffix is viewed with its exact seeded x4
carry.  If its information digits avoid BIG1, the finite natural support forces
an extremely rigid language.

At seed 3 the only nonterminal BIG1-free bad cycle is

  (carry,digit) = (3,0) -> (1,2) -> (3,0) -> ...

and at seed 2 the only nonterminal entrance is digit 2 into that same cycle.
Consequently the suffix has a closed base-nine form.  When inserted into the
canonical horizontal trap peel `X = C + 4*Y`, the supposedly BIG1-free suffix
becomes an explicit BIG1 object:

  C=3 : X = 3*9^r = 3^(2r+1)
  C=2 : X = 9^r+1 = 3^(2r)+1.
-/

def GSTSleepSeededBadTraceS (D X : Nat) : Prop :=
  ∀ j, GSTBadPairS (gstAffineCarryS D X j) (gstDigitS X j)

def GSTSleepNoBig1S (X : Nat) : Prop :=
  ∀ j, gstDigitS X j ≠ 1

/-- Exact seeded carry semigroup for suffix reindexing. -/
theorem gst_sleep_affine_carry_semigroupS
    (D X q j : Nat) :
    gstAffineCarryS D X (q+j) =
      gstAffineCarryS (gstAffineCarryS D X q) (X / 3^q) j := by
  simp only [gstAffineCarryS]
  rw [Nat.pow_add, Nat.mod_mul]
  have hqpos : 0 < 3^q := Nat.pow_pos (by decide)
  have hshape :
      D + 4 * (X % 3^q + 3^q * (X / 3^q % 3^j)) =
        (D + 4 * (X % 3^q)) +
          3^q * (4 * (X / 3^q % 3^j)) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hqpos]

/-- Exact digit suffix shift. -/
theorem gst_sleep_digit_shiftS (X q j : Nat) :
    gstDigitS X (q+j) = gstDigitS (X / 3^q) j := by
  simp only [gstDigitS]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- Complete badness survives exact suffix reindexing with the true regenerated
seed. -/
theorem gst_sleep_bad_suffixS
    (D X q : Nat)
    (hbad : GSTSleepSeededBadTraceS D X) :
    GSTSleepSeededBadTraceS
      (gstAffineCarryS D X q) (X / 3^q) := by
  intro j
  have hj := hbad (q+j)
  rw [gst_sleep_affine_carry_semigroupS,
    gst_sleep_digit_shiftS] at hj
  exact hj

/-- BIG1-clear information also survives suffix reindexing. -/
theorem gst_sleep_noBig1_suffixS
    (X q : Nat) (hno : GSTSleepNoBig1S X) :
    GSTSleepNoBig1S (X / 3^q) := by
  intro j
  rw [← gst_sleep_digit_shiftS X q j]
  exact hno (q+j)

/-- Seed zero + complete badness + no BIG1 leaves only the zero word. -/
theorem gst_sleep_seed_zero_noBig1_bad_is_zeroS :
    ∀ X : Nat,
      GSTSleepSeededBadTraceS 0 X → GSTSleepNoBig1S X → X = 0 := by
  intro X
  induction X using Nat.strongRecOn with
  | ind X ih =>
      intro hbad hno
      by_cases hX0 : X = 0
      · exact hX0
      have hd2 : X % 3 ≠ 2 := by
        intro hx
        have hbad0 := hbad 0
        apply hbad0
        constructor
        · simpa [gstDigitS] using hx
        · left
          simp [gstAffineCarryS, Nat.mod_one]
      have hd1 : X % 3 ≠ 1 := by
        have h := hno 0
        simpa [GSTSleepNoBig1S, gstDigitS] using h
      have hmodlt : X % 3 < 3 := Nat.mod_lt _ (by decide)
      have hmod0 : X % 3 = 0 := by omega
      have hbadTail0 := gst_sleep_bad_suffixS 0 X 1 hbad
      have hbadTail : GSTSleepSeededBadTraceS 0 (X/3) := by
        simpa [gstAffineCarryS, hmod0] using hbadTail0
      have hnoTail0 := gst_sleep_noBig1_suffixS X 1 hno
      have hnoTail : GSTSleepNoBig1S (X/3) := by
        simpa using hnoTail0
      have hlt : X/3 < X := Nat.div_lt_self (by omega) (by decide)
      have htail0 : X/3 = 0 := ih (X/3) hlt hbadTail hnoTail
      have hsplit := Nat.mod_add_div X 3
      omega

/-- Seed one and seed three collapse simultaneously. -/
theorem gst_sleep_seed_one_three_noBig1_bad_formsS :
    ∀ X : Nat,
      (GSTSleepSeededBadTraceS 1 X → GSTSleepNoBig1S X →
        ∃ r, 4*X = 9^r - 1) ∧
      (GSTSleepSeededBadTraceS 3 X → GSTSleepNoBig1S X →
        ∃ r, 4*X = 3 * (9^r - 1)) := by
  intro X
  induction X using Nat.strongRecOn with
  | ind X ih =>
      constructor
      · intro hbad hno
        by_cases hX0 : X = 0
        · subst X
          exact ⟨0, by decide⟩
        have hd1 : X % 3 ≠ 1 := by
          have h := hno 0
          simpa [GSTSleepNoBig1S, gstDigitS] using h
        have hmodlt : X % 3 < 3 := Nat.mod_lt _ (by decide)
        have hcase : X % 3 = 0 ∨ X % 3 = 2 := by omega
        rcases hcase with hmod0 | hmod2
        · have hbadTail0 := gst_sleep_bad_suffixS 1 X 1 hbad
          have hbadTail : GSTSleepSeededBadTraceS 0 (X/3) := by
            simpa [gstAffineCarryS, hmod0] using hbadTail0
          have hnoTail : GSTSleepNoBig1S (X/3) := by
            simpa using gst_sleep_noBig1_suffixS X 1 hno
          have htail0 :=
            gst_sleep_seed_zero_noBig1_bad_is_zeroS (X/3) hbadTail hnoTail
          have hsplit := Nat.mod_add_div X 3
          exfalso
          omega
        · have hbadTail0 := gst_sleep_bad_suffixS 1 X 1 hbad
          have hbadTail : GSTSleepSeededBadTraceS 3 (X/3) := by
            simpa [gstAffineCarryS, hmod2] using hbadTail0
          have hnoTail : GSTSleepNoBig1S (X/3) := by
            simpa using gst_sleep_noBig1_suffixS X 1 hno
          have hlt : X/3 < X := Nat.div_lt_self (by omega) (by decide)
          obtain ⟨r, hr⟩ := (ih (X/3) hlt).2 hbadTail hnoTail
          refine ⟨r+1, ?_⟩
          have hsplit := Nat.mod_add_div X 3
          have hp : 0 < 9^r := Nat.pow_pos (by decide)
          rw [Nat.pow_succ]
          omega
      · intro hbad hno
        by_cases hX0 : X = 0
        · subst X
          exact ⟨0, by decide⟩
        have hd2 : X % 3 ≠ 2 := by
          intro hx
          have hbad0 := hbad 0
          apply hbad0
          constructor
          · simpa [gstDigitS] using hx
          · right
            simp [gstAffineCarryS, Nat.mod_one]
        have hd1 : X % 3 ≠ 1 := by
          have h := hno 0
          simpa [GSTSleepNoBig1S, gstDigitS] using h
        have hmodlt : X % 3 < 3 := Nat.mod_lt _ (by decide)
        have hmod0 : X % 3 = 0 := by omega
        have hbadTail0 := gst_sleep_bad_suffixS 3 X 1 hbad
        have hbadTail : GSTSleepSeededBadTraceS 1 (X/3) := by
          simpa [gstAffineCarryS, hmod0] using hbadTail0
        have hnoTail : GSTSleepNoBig1S (X/3) := by
          simpa using gst_sleep_noBig1_suffixS X 1 hno
        have hlt : X/3 < X := Nat.div_lt_self (by omega) (by decide)
        obtain ⟨r, hr⟩ := (ih (X/3) hlt).1 hbadTail hnoTail
        refine ⟨r, ?_⟩
        have hsplit := Nat.mod_add_div X 3
        omega

/-- Seed two has the same base-nine closed form as seed one. -/
theorem gst_sleep_seed_two_noBig1_bad_formS
    (X : Nat)
    (hbad : GSTSleepSeededBadTraceS 2 X)
    (hno : GSTSleepNoBig1S X) :
    ∃ r, 4*X = 9^r - 1 := by
  by_cases hX0 : X = 0
  · subst X
    exact ⟨0, by decide⟩
  have hd1 : X % 3 ≠ 1 := by
    have h := hno 0
    simpa [GSTSleepNoBig1S, gstDigitS] using h
  have hmodlt : X % 3 < 3 := Nat.mod_lt _ (by decide)
  have hcase : X % 3 = 0 ∨ X % 3 = 2 := by omega
  rcases hcase with hmod0 | hmod2
  · have hbadTail0 := gst_sleep_bad_suffixS 2 X 1 hbad
    have hbadTail : GSTSleepSeededBadTraceS 0 (X/3) := by
      simpa [gstAffineCarryS, hmod0] using hbadTail0
    have hnoTail : GSTSleepNoBig1S (X/3) := by
      simpa using gst_sleep_noBig1_suffixS X 1 hno
    have htail0 :=
      gst_sleep_seed_zero_noBig1_bad_is_zeroS (X/3) hbadTail hnoTail
    have hsplit := Nat.mod_add_div X 3
    exfalso
    omega
  · have hbadTail0 := gst_sleep_bad_suffixS 2 X 1 hbad
    have hbadTail : GSTSleepSeededBadTraceS 3 (X/3) := by
      simpa [gstAffineCarryS, hmod2] using hbadTail0
    have hnoTail : GSTSleepNoBig1S (X/3) := by
      simpa using gst_sleep_noBig1_suffixS X 1 hno
    obtain ⟨r, hr⟩ :=
      (gst_sleep_seed_one_three_noBig1_bad_formsS (X/3)).2
        hbadTail hnoTail
    refine ⟨r+1, ?_⟩
    have hsplit := Nat.mod_add_div X 3
    have hp : 0 < 9^r := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

/-- The exact horizontal-peel child `C+4Y` becomes a closed ternary BIG1
object on either possible post-last-gate seed. -/
theorem gst_sleep_big1_free_last_gate_peel_formsS
    (C Y : Nat)
    (hC : C = 2 ∨ C = 3)
    (hbad : GSTSleepSeededBadTraceS C Y)
    (hno : GSTSleepNoBig1S Y) :
    (∃ r, C = 2 ∧ C + 4*Y = 9^r + 1) ∨
      (∃ r, C = 3 ∧ C + 4*Y = 3 * 9^r) := by
  rcases hC with rfl | rfl
  · obtain ⟨r, hr⟩ := gst_sleep_seed_two_noBig1_bad_formS Y hbad hno
    left
    refine ⟨r, rfl, ?_⟩
    have hp : 0 < 9^r := Nat.pow_pos (by decide)
    omega
  · obtain ⟨r, hr⟩ :=
      (gst_sleep_seed_one_three_noBig1_bad_formsS Y).2 hbad hno
    right
    refine ⟨r, rfl, ?_⟩
    have hp : 0 < 9^r := Nat.pow_pos (by decide)
    omega

/-- Same result in pure ternary-power form. -/
theorem gst_sleep_big1_free_last_gate_peel_is_ternary_boundaryS
    (C Y : Nat)
    (hC : C = 2 ∨ C = 3)
    (hbad : GSTSleepSeededBadTraceS C Y)
    (hno : GSTSleepNoBig1S Y) :
    (∃ r, C + 4*Y = 3^(2*r) + 1) ∨
      (∃ r, C + 4*Y = 3^(2*r+1)) := by
  rcases gst_sleep_big1_free_last_gate_peel_formsS C Y hC hbad hno with h2 | h3
  · obtain ⟨r, _hC2, hX⟩ := h2
    left
    refine ⟨r, ?_⟩
    have hpow : 9^r = 3^(2*r) := by
      rw [show (9:Nat) = 3^2 by decide, ← Nat.pow_mul]
    rw [hpow] at hX
    exact hX
  · obtain ⟨r, _hC3, hX⟩ := h3
    right
    refine ⟨r, ?_⟩
    have hpow : 3 * 9^r = 3^(2*r+1) := by
      rw [show (9:Nat) = 3^2 by decide, ← Nat.pow_mul,
        show 2*r+1 = 1 + 2*r by omega, Nat.pow_add]
    exact hX.trans hpow

#check gst_sleep_seed_zero_noBig1_bad_is_zeroS
#check gst_sleep_seed_one_three_noBig1_bad_formsS
#check gst_sleep_seed_two_noBig1_bad_formS
#check gst_sleep_big1_free_last_gate_peel_formsS
#check gst_sleep_big1_free_last_gate_peel_is_ternary_boundaryS

#print axioms gst_sleep_big1_free_last_gate_peel_is_ternary_boundaryS

end GSTInfiniteV2
