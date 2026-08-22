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

/-- **Mixed 2D GST emergence equation.**

The handwritten seven-kernel and U operator are not separately forced into a
2D model.  Their exact physical-cell combination `8*K + 7*U` *becomes* a
horizontal information boundary derivative, a vertical carry derivative, and
one positive interior SURVIVE source.

The coefficient ratio is the one for which the horizontal potential agrees on
BIG0 and BIG2, leaving BIG1 as the unique horizontal defect. -/
theorem mixed_cell_emergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    8 * sevenKernel C d + 7 * uJump C d =
      infoPotential (outDigit C d) - infoPotential d +
      7 * carryPotential C - 21 * carryPotential (nextCarry C d) +
      56 * surviveI C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [sevenKernel, surviveI, twoI, uJump, uCharge,
      outDigit, nextCarry, carryPotential, infoPotential]

#check mixed_cell_emergence
#print axioms mixed_cell_emergence

end GST2DMixedEmergence
