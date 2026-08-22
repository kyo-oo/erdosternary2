import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GST2DMixedEmergence

/-- Exact x4/base-3 cell output digit. -/
def outDigit (C d : Nat) : Nat := (C + 4*d) % 3

/-- Exact x4/base-3 next carry. -/
def nextCarry (C d : Nat) : Nat := (C + 4*d) / 3

/-- Handwritten U charge chart. -/
def uCharge (C : Nat) : Int :=
  if C = 0 then 5 else if C = 3 then 21 else 15

/-- Handwritten U jump. -/
def uJump (C d : Nat) : Int :=
  3 * uCharge (nextCarry C d) - uCharge C - 24*(d : Int)

/-- Indicator of information digit BIG2. -/
def twoI (d : Nat) : Int := if d = 2 then 1 else 0

/-- A physical x4 SURVIVE incidence: BIG2 enters and BIG2 leaves. -/
def surviveI (C d : Nat) : Int :=
  if d = 2 ∧ outDigit C d = 2 then 1 else 0

/-- Coarse signed seven-kernel of one x4 cell. -/
def sevenKernel (C d : Nat) : Int :=
  14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d

/-- Vertical carry potential selected by the exact twelve-cell system. -/
def carryPotential (C : Nat) : Int :=
  if C = 0 then -5 else if C = 1 then -7 else if C = 2 then 1 else 3

/-- Horizontal information potential.  It vanishes on BIG0 and BIG2 and is
`-56` exactly on BIG1. -/
def infoPotential (d : Nat) : Int :=
  112 * twoI d - 56*(d : Int)

def mixedDensity (C d : Nat) : Int :=
  8 * sevenKernel C d + 7 * uJump C d

/-- The mixed horizontal potential is exactly the BIG1 detector on physical
ternary digits. -/
theorem infoPotential_physical_table
    (d : Nat) (hd : d < 3) :
    (d = 0 ∧ infoPotential d = 0) ∨
    (d = 1 ∧ infoPotential d = -56) ∨
    (d = 2 ∧ infoPotential d = 0) := by
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hdc with rfl | rfl | rfl <;>
    norm_num [infoPotential, twoI]

/-- The U operator by itself is already a two-direction divergence: horizontal
information transport plus the ternary carry-potential derivative. -/
theorem uJump_divergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    uJump C d =
      8 * ((d : Int) - (outDigit C d : Int)) +
      carryPotential C - 3 * carryPotential (nextCarry C d) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [uJump, uCharge, outDigit, nextCarry, carryPotential]

/-- **Mixed 2D GST emergence equation.** -/
theorem mixed_cell_emergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    mixedDensity C d =
      infoPotential (outDigit C d) - infoPotential d +
      7 * carryPotential C - 21 * carryPotential (nextCarry C d) +
      56 * surviveI C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [mixedDensity, sevenKernel, surviveI, twoI, uJump, uCharge,
      outDigit, nextCarry, carryPotential, infoPotential]

/-- Ordinary horizontal discrete derivative. -/
theorem horizontal_diff_telescope (f : Nat → Int) (N : Nat) :
    Finset.sum (Finset.range N) (fun t => f (t+1) - f t) =
      f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- One horizontal row of physical x4 cells. -/
theorem mixed_row_emergence
    (C Cnext d : Nat → Nat) (N : Nat)
    (hcell : ∀ t, t < N →
      C t < 4 ∧ d t < 3 ∧
      outDigit (C t) (d t) = d (t+1) ∧
      nextCarry (C t) (d t) = Cnext t) :
    Finset.sum (Finset.range N) (fun t => mixedDensity (C t) (d t)) =
      infoPotential (d N) - infoPotential (d 0) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t)) -
        3 * Finset.sum (Finset.range N) (fun t => carryPotential (Cnext t))) +
      56 * Finset.sum (Finset.range N) (fun t => surviveI (C t) (d t)) := by
  have hlocal :
      Finset.sum (Finset.range N) (fun t => mixedDensity (C t) (d t)) =
        Finset.sum (Finset.range N) (fun t =>
          (infoPotential (d (t+1)) - infoPotential (d t)) +
          (7 * carryPotential (C t) - 21 * carryPotential (Cnext t)) +
          56 * surviveI (C t) (d t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    rcases hcell t (Finset.mem_range.mp ht) with ⟨hC, hd, hout, hnext⟩
    rw [mixed_cell_emergence (C t) (d t) hC hd, hout, hnext]
    ring
  rw [hlocal, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [horizontal_diff_telescope]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Full 2D divergence theorem.** Every finite rectangle cut from the live
Nat×Nat grid has only left/right BIG1 boundary charge, bottom/top carry flux,
and positive interior SURVIVE incidence. The top boundary is retained; no
terminal state or support horizon occurs. -/
theorem mixed_rectangle_emergence
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
        mixedDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * (infoPotential (d N p) - infoPotential (d 0 p))) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t 0)) -
        (3 : Int)^K * Finset.sum (Finset.range N) (fun t => carryPotential (C t K))) +
      56 * Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
          surviveI (C t p) (d t p))) := by
  omega

#check mixed_cell_emergence
#check mixed_rectangle_emergence
#print axioms mixed_cell_emergence
#print axioms mixed_rectangle_emergence

end GST2DMixedEmergence
