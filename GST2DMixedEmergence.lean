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

/-- Desired local mixed 2D equation.  The `56*surviveI` term is the interior
source; `infoPotential` is the horizontal BIG1 boundary flux and
`carryPotential` is the vertical carry flux. -/
theorem mixed_cell_emergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    8 * sevenKernel C d + 7 * uJump C d =
      infoPotential (outDigit C d) - infoPotential d +
      7 * carryPotential C - 21 * carryPotential (nextCarry C d) +
      56 * surviveI C d := by
  omega

end GST2DMixedEmergence
