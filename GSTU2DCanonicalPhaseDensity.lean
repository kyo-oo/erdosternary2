import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DCanonicalPhaseDensity

open GST2DMixedEmergence
open GSTU2DEventTransport

/-- Minimal ternary information potential. On physical digits it is exactly d-1. -/
def phaseDigitPotential (d : Nat) : Int :=
  (d : Int) - 1

/-- Monotone carry potential selected by the exact twelve-state x4/base3 table. -/
def phaseCarryPotential (C : Nat) : Int :=
  if C = 0 then 2 else if C = 1 then 1 else 0

/-- Canonical phase density.  Its divergence coefficients are the literal GST
horizontal factor 1 and vertical factor 3. -/
def phaseDensity (C d : Nat) : Int :=
  phaseDigitPotential (outDigit C d) - phaseDigitPotential d +
    phaseCarryPotential C - 3 * phaseCarryPotential (nextCarry C d) +
    surviveI C d

/-- RED/GREEN finite-state target: both Happy cells are +2; all ten bad cells
are nonpositive, with global floor -4. -/
theorem phaseDensity_physical_table :
    phaseDensity 0 0 = -4 ∧ phaseDensity 0 1 = -1 ∧
    phaseDensity 0 2 = 2 ∧
    phaseDensity 1 0 = -4 ∧ phaseDensity 1 1 = 0 ∧
    phaseDensity 1 2 = -1 ∧
    phaseDensity 2 0 = -4 ∧ phaseDensity 2 1 = -1 ∧
    phaseDensity 2 2 = 0 ∧
    phaseDensity 3 0 = -3 ∧ phaseDensity 3 1 = 0 ∧
    phaseDensity 3 2 = 2 := by
  decide

/-- Happy is exactly the positive sector of the new density. -/
theorem happy_iff_phaseDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < phaseDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    decide

/-- Uniform physical floor used by highest-row domination. -/
theorem phaseDensity_ge_neg_four
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-4 : Int) ≤ phaseDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    decide

/-- Non-Happy is exactly nonpositive on physical cells. -/
theorem phaseDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    phaseDensity C d ≤ 0 := by
  have hiff := happy_iff_phaseDensity_positive C d hC hd
  by_contra hnot
  have hpos : 0 < phaseDensity C d := by omega
  exact hbad (hiff.mpr hpos)

/-- Base-three weighted prefix of one vertical graph column. -/
def weightedPhaseColumnPrefix
    (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | K+1 => weightedPhaseColumnPrefix C d K +
      (((3^K : Nat) : Int)) * phaseDensity (C K) (d K)

/-- Sharp one-column domination: if the top row q is Happy, its +2*3^q source
beats the exact worst-case -4 contribution of all lower rows. -/
theorem weightedPhaseColumnPrefix_positive_of_top_happy
    (C d : Nat → Nat) (q : Nat)
    (hC : ∀ p, p ≤ q → C p < 4)
    (hd : ∀ p, p ≤ q → d p < 3)
    (hHappy : HappyCell (C q) (d q)) :
    0 < weightedPhaseColumnPrefix C d (q+1) := by
  have htop : phaseDensity (C q) (d q) = 2 := by
    have hiff := happy_iff_phaseDensity_positive (C q) (d q)
      (hC q (by omega)) (hd q (by omega))
    have hp := hiff.mp hHappy
    have hlt := phaseDensity_ge_neg_four (C q) (d q)
      (hC q (by omega)) (hd q (by omega))
    have htab := phaseDensity_physical_table
    have hCc : C q = 0 ∨ C q = 1 ∨ C q = 2 ∨ C q = 3 := by
      have := hC q (by omega); omega
    have hdc : d q = 0 ∨ d q = 1 ∨ d q = 2 := by
      have := hd q (by omega); omega
    rcases hCc with h0 | h1 | h2 | h3 <;>
      rcases hdc with d0 | d1 | d2 <;>
      subst C q <;> subst d q <;> simp [HappyCell] at hHappy ⊢
  have hlower :
      (-2 : Int) * ((((3^q : Nat) : Int)) - 1) ≤
        weightedPhaseColumnPrefix C d q := by
    induction q with
    | zero => simp [weightedPhaseColumnPrefix]
    | succ q ih =>
        have ih' := ih
          (fun p hp => hC p (by omega))
          (fun p hp => hd p (by omega))
        have hfloor := phaseDensity_ge_neg_four (C q) (d q)
          (hC q (by omega)) (hd q (by omega))
        have hw : (0 : Int) ≤ (((3^q : Nat) : Int)) := by positivity
        have hwfloor := mul_le_mul_of_nonneg_left hfloor hw
        have hpow :
            (((3^(q+1) : Nat) : Int)) = 3 * (((3^q : Nat) : Int)) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        rw [weightedPhaseColumnPrefix, hpow]
        calc
          (-2 : Int) * (3 * (((3^q : Nat) : Int)) - 1) =
              (-2 : Int) * ((((3^q : Nat) : Int)) - 1) +
                (((3^q : Nat) : Int)) * (-4) := by ring
          _ ≤ weightedPhaseColumnPrefix C d q +
                (((3^q : Nat) : Int)) * phaseDensity (C q) (d q) :=
            add_le_add ih' (by simpa [mul_comm] using hwfloor)
  rw [weightedPhaseColumnPrefix, htop]
  have hpowpos : 0 < (((3^q : Nat) : Int)) := by positivity
  nlinarith

/-- Horizontal digit potential telescopes because the coefficient is exactly one. -/
theorem horizontal_phase_digit_telescope
    (d : Nat → Nat) (N : Nat) :
    Finset.sum (Finset.range N) (fun t =>
      phaseDigitPotential (d (t+1)) - phaseDigitPotential (d t)) =
      phaseDigitPotential (d N) - phaseDigitPotential (d 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Vertical base-three carry potential telescopes exactly. -/
theorem vertical_phase_carry_telescope
    (C : Nat → Nat) (K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        (phaseCarryPotential (C p) - 3 * phaseCarryPotential (C (p+1))) ) =
      phaseCarryPotential (C 0) -
        (((3^K : Nat) : Int)) * phaseCarryPotential (C K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      push_cast
      ring

/-- Exact 2D rectangle identity for the new phase density. The only interior
term is the nonnegative microscopic SURVIVE incidence. -/
theorem phaseRectangle_exact
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range N) (fun t =>
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (d N p) - phaseDigitPotential (d 0 p))) +
      Finset.sum (Finset.range N) (fun t => phaseCarryPotential (C t 0)) -
        (((3^K : Nat) : Int)) *
          Finset.sum (Finset.range N) (fun t => phaseCarryPotential (C t K)) +
      Finset.sum (Finset.range N) (fun t =>
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) * surviveI (C t p) (d t p))) := by
  have hrow : ∀ t, t < N →
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C t p) (d t p)) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (d (t+1) p) - phaseDigitPotential (d t p))) +
      phaseCarryPotential (C t 0) -
        (((3^K : Nat) : Int)) * phaseCarryPotential (C t K) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * surviveI (C t p) (d t p)) := by
    intro t ht
    have hlocal :
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) * phaseDensity (C t p) (d t p)) =
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) *
            ((phaseDigitPotential (d (t+1) p) - phaseDigitPotential (d t p)) +
             (phaseCarryPotential (C t p) - 3 * phaseCarryPotential (C t (p+1))) +
             surviveI (C t p) (d t p))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpK := Finset.mem_range.mp hp
      have hc := hcell t p ht hpK
      rw [phaseDensity, hc.2.2.1, hc.2.2.2]
      ring
    rw [hlocal]
    have hcarry := vertical_phase_carry_telescope (fun p => C t p) K
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [hcarry]
    ring
  calc
    Finset.sum (Finset.range N) (fun t =>
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C t p) (d t p))) =
      Finset.sum (Finset.range N) (fun t =>
        (Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) *
            (phaseDigitPotential (d (t+1) p) - phaseDigitPotential (d t p))) +
        phaseCarryPotential (C t 0) -
          (((3^K : Nat) : Int)) * phaseCarryPotential (C t K) +
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) * surviveI (C t p) (d t p)))) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hrow t (Finset.mem_range.mp ht)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      have hdTel : ∀ p, p < K →
          Finset.sum (Finset.range N) (fun t =>
            phaseDigitPotential (d (t+1) p) - phaseDigitPotential (d t p)) =
            phaseDigitPotential (d N p) - phaseDigitPotential (d 0 p) := by
        intro p hp
        exact horizontal_phase_digit_telescope (fun t => d t p) N
      rw [Finset.sum_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.mul_sum]
        rw [hdTel p (Finset.mem_range.mp hp)]
      · ring

#check phaseDensity_physical_table
#check happy_iff_phaseDensity_positive
#check weightedPhaseColumnPrefix_positive_of_top_happy
#check phaseRectangle_exact
#print axioms phaseDensity_physical_table
#print axioms weightedPhaseColumnPrefix_positive_of_top_happy
#print axioms phaseRectangle_exact

end GSTU2DCanonicalPhaseDensity
