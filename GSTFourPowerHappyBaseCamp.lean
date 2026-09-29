import ErdosTernary2
import GSTCanonicalTailStateIso
import GSTInfiniteFourPowerNavigation
import GSTFourPowerDirectExistenceFromHappy
import GSTHypothesisToTheorem

/-!
# The Happy Climb Base Camp and the Tail Reduction

The third-wave climb — `∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p)
(digit3 (4^K) p)` — is the single named input of the entire four-power
chain: it delivers the creation master through the FromHappy bridge, and
the master feeds both the hypothesis-to-theorem conversion (the crown) and
the k=1 Ω-termination (the residual route).  The worldtrace simulation
certified the climb empirically at N = 1500; this file converts the
empirical certification below 501 into kernel-checked ground truth.

## The base camp (kernel receipts)

`four_power_happy_climb_base`: every exponent `K` in `[8, 500]` owns a
physical Happy row at a ternary position `p` with `3 ≤ p < 48`.  The proof
is a single kernel `decide` over `k < 501` on a 48-trit window of `4^k`,
computed by the monolith's own `powMod` — the identical pattern as the
CI-green `modular_check_base` (which kernel-checks digit-2 existence on
the same exponent range at a 12-trit window).

## The tail reduction (the war's remaining object, shrunk)

`four_power_happy_climb_tail`: every exponent `K > 500` owns a physical
Happy row.  From the base camp plus the tail:

* `four_power_happy_climb_of_tail` assembles the FULL climb;
* `fourPowerCreationMaster_of_base_and_tail` delivers the creation master
  through the green FromHappy bridge (rows 5 and 6 by the kernel residue
  classifier, `K = 7` excluded by the hypothesis statement itself);
* `erdos_ternary_2_universal_of_climb_tail` — **THE CROWN FROM THE TAIL**:
  the full Erdős ternary-2 theorem `∀ n ≥ 9, noTernaryTwo (2^n) = false`
  from the tail premise alone, through the hypothesis-to-theorem
  conversion and the conjecture-form crown of the monolith;
* `gst_omega_termination_s1_of_climb_tail` — the k=1 Ω-termination from
  the same premise: one socket, both routes.

The war's remaining content is ONE named object: the tail climb.  Every
other link — the base camp, the residue rows, the master bridge, the
conversion, the crown, the termination — is machine-checked.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerHappyBaseCamp

open GSTCanonicalTailStateIso
open GSTInfiniteFourPowerNavigation
open GSTFourPowerDirectExistenceFromHappy
open GSTHypothesisToTheorem

/-! ## Section 0 — the kernel window scan -/

/-- Bool scan of the low `B` ternary positions of `n`: is there a Happy
cell (digit two, x4-carry zero or three) at a position `p` with `3 ≤ p`?
Positions are visited top-down; the window is exact because digits and
x4-carries at positions below `B` depend only on `n mod 3^B`. -/
def happyBelow : Nat → Nat → Bool
  | _, 0 => false
  | n, p+1 =>
      if 3 ≤ p ∧ (n / 3^p) % 3 = 2 ∧
          ((4 * (n % 3^p)) / 3^p = 0 ∨ (4 * (n % 3^p)) / 3^p = 3)
      then true
      else happyBelow n p

/-- THE KERNEL RECEIPT.  Every exponent below 501 either is below eight or
owns a Happy row inside its 48-trit window.  Same quantifier shape and
same `powMod` pattern as the CI-green `modular_check_base` easy range. -/
theorem happy_scan_receipt :
    ∀ k < 501,
      happyBelow (powMod 4 k (3^48)) 48 = true ∨ k < 8 := by
  decide

/-- Scan extraction: a true window scan is a literal Happy cell inside the
window. -/
theorem exists_happy_of_happyBelow :
    ∀ (B n : Nat), happyBelow n B = true →
      ∃ p : Nat, 3 ≤ p ∧ p < B ∧
        HappyCell (carry4 n p) (digit3 n p) := by
  intro B
  induction B with
  | zero => intro n h; simp [happyBelow] at h
  | succ B ih =>
      intro n h
      simp only [happyBelow] at h
      split at h
      · rename_i hcond
        exact ⟨B, hcond.1, by omega,
          ⟨by unfold digit3; exact hcond.2.1,
            by unfold carry4; exact hcond.2.2⟩⟩
      · obtain ⟨p, hp3, hpB, hcell⟩ := ih n h
        exact ⟨p, hp3, by omega, hcell⟩

/-- The x4-carry at a position below the window bound is untouched by the
window reduction: carries at positions `≤ B` depend only on `R mod 3^B`. -/
theorem carry4_mod_window (R B p : Nat) (hpB : p ≤ B) :
    carry4 (R % 3^B) p = carry4 R p := by
  unfold carry4
  rw [Nat.mod_mod_of_dvd R (Nat.pow_dvd_pow 3 hpB)]

/-- The ternary digit at a position strictly below the window bound is
untouched by the window reduction: `R = 3^B·Q + S` splits the division by
`3^p` into a multiple of three plus the window's own digit. -/
theorem digit3_mod_window (R B p : Nat) (hp : p < B) :
    digit3 (R % 3^B) p = digit3 R p := by
  unfold digit3
  have h3p : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : 3^B = 3^p * 3^(B - p) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hfac : 3^B * (R / 3^B) = 3^p * (3^(B - p) * (R / 3^B)) := by
    rw [← Nat.mul_assoc, ← hsplit]
  have hR : R = 3^p * (3^(B - p) * (R / 3^B)) + R % 3^B := by
    have hdm : 3^B * (R / 3^B) + R % 3^B = R := Nat.div_add_mod R (3^B)
    omega
  conv_rhs => rw [hR, Nat.add_comm, Nat.add_mul_div_left _ _ h3p]
  have hzero : (3^(B - p) * (R / 3^B)) % 3 = 0 := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : B - p ≠ 0) with ⟨m, hm⟩
    rw [hm, Nat.pow_succ]
    simp [Nat.mul_mod]
  rw [Nat.add_mod, hzero, Nat.add_zero, Nat.mod_mod]

/-- A Happy cell of the window-reduced power is a Happy cell of the power
itself, inside the window. -/
theorem happy_cell_pow_mod (K B p : Nat) (hp : p < B)
    (h : HappyCell (carry4 (powMod 4 K (3^B)) p) (digit3 (powMod 4 K (3^B)) p)) :
    HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  have hB1 : 1 ≤ B := by omega
  have h9 : (3 : Nat) ≤ 3^B :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hB1
  have hpm : powMod 4 K (3^B) = 4^K % 3^B :=
    powMod_correct 4 K (3^B) (by omega)
  rw [hpm] at h
  rw [carry4_mod_window (4^K) B p (Nat.le_of_lt hp),
    digit3_mod_window (4^K) B p hp] at h
  exact h

/-! ## Section 1 — the base camp -/

/-- **THE BASE CAMP.**  Every exponent `K` in `[8, 500]` owns a physical
Happy row at a ternary position at least three — kernel-checked, on the
monolith's own `powMod` window pattern. -/
theorem four_power_happy_climb_base
    (K : Nat) (hK8 : 8 ≤ K) (hK500 : K ≤ 500) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  have hkey := happy_scan_receipt K (by omega)
  rcases hkey with hscan | hlt8
  · obtain ⟨p, hp3, hp48, hcell⟩ :=
      exists_happy_of_happyBelow 48 (powMod 4 K (3^48)) hscan
    exact ⟨p, hp3, happy_cell_pow_mod K 48 p hp48 hcell⟩
  · omega

/-! ## Section 2 — the tail: the war's remaining object, shrunk -/

/-- THE TAIL CLIMB — the war's entire remaining content in one named
`Prop`: every exponent above the kernel-checked base camp owns a physical
Happy row at a ternary position at least three. -/
def four_power_happy_climb_tail : Prop :=
  ∀ K : Nat, 500 < K →
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)

/-- The full climb assembles from the base camp plus the tail. -/
theorem four_power_happy_climb_of_tail
    (htail : four_power_happy_climb_tail) :
    GSTInfiniteFourPowerNavigation.four_power_happy_climb := by
  intro K hK8
  by_cases hK500 : K ≤ 500
  · exact four_power_happy_climb_base K hK8 hK500
  · exact htail K (by omega)

/-- The creation master from the base camp plus the tail, through the
green FromHappy bridge (rows five and six by the kernel residue
classifier, the excluded row seven never enters). -/
theorem fourPowerCreationMaster_of_base_and_tail
    (htail : four_power_happy_climb_tail) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster :=
  fourPowerCreationMaster_direct (four_power_happy_climb_of_tail htail)

/-- The even-power theorem from the tail premise, through the
hypothesis-to-theorem conversion's two-wave route. -/
theorem erdos_ternary_2_even_universal_of_climb_tail
    (htail : four_power_happy_climb_tail)
    (a : Nat) (ha : 5 ≤ a) :
    hasTernaryTwo (4^a) = true :=
  erdos_ternary_2_even_universal_of_hypothesis
    (fourPowerCreationMaster_of_base_and_tail htail) a ha

/-- **THE CROWN FROM THE TAIL.**  The full Erdős ternary-2 theorem — every
`2^n` with `n ≥ 9` has a ternary digit two — from the tail climb alone.
Below the base camp the kernel carries the even rows and the monolith's
odd theorem carries the rest; above it the tail feeds the master, the
master feeds the conversion, the conversion feeds the conjecture-form
crown.  One named premise, one machine-checked implication. -/
theorem erdos_ternary_2_universal_of_climb_tail
    (htail : four_power_happy_climb_tail)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_even_conjecture
    (fun K _hK8 =>
      has_two_imp_not_no_two (4^K)
        (erdos_ternary_2_even_universal_of_climb_tail htail K (by omega)))
    n hn

/-- The k=1 Ω-termination from the same premise — the residual route
plugs into the same socket: the master from the tail closes the atomic
seam exactly as the hypothesis does. -/
theorem gst_omega_termination_s1_of_climb_tail
    (htail : four_power_happy_climb_tail)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ¬ GSTOmegaInfiniteBadTrace s 1 n :=
  gst_omega_termination_s1_of_hypothesis
    (fourPowerCreationMaster_of_base_and_tail htail) s n hs hn hchild

/-! ## Section 3 — receipts -/

#print axioms four_power_happy_climb_base
#print axioms four_power_happy_climb_of_tail
#print axioms fourPowerCreationMaster_of_base_and_tail
#print axioms erdos_ternary_2_even_universal_of_climb_tail
#print axioms erdos_ternary_2_universal_of_climb_tail
#print axioms gst_omega_termination_s1_of_climb_tail

end GSTFourPowerHappyBaseCamp
