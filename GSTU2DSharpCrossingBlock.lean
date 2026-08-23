import GSTU2DExactCrossingCharge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DExactCrossingCharge

open GST2DMixedEmergence
open GSTU2DEventTransport

/-- Terminal digit potential for the sharp horizontal crossing certificate.
The values are the exact finite-state Bellman certificate for the twelve
physical x4/base-3 cells. -/
def sharpTerminalPotential (d : Nat) : Int :=
  if d = 0 then 176 else if d = 1 then 185 else 149

/-- One physical x4 step preserves the sharp crossing certificate.  This is a
complete twelve-state check; unlike the coarse `-111` estimate it uses the
actual emitted ternary digit. -/
theorem sharpTerminalPotential_step
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    sharpTerminalPotential (outDigit C d) ≤
      4 * sharpTerminalPotential d + 5 * crossDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [sharpTerminalPotential, crossDensity, digitPotential,
      carryPotentialX, outDigit, nextCarry, surviveI, midDigit,
      finalMicroDigit, microOutput, highBit, lowBit, twoI]

/-- Sharp all-width no-erasure bound for a physical horizontal row beginning
at a Happy cell.  The old scalar envelope `17*4^N+37` forgets the emitted
ternary state.  Retaining that state gives the stronger exact certificate

  `94*4^N + P(d_N) ≤ 5*reverseCrossCode`,

with `P ∈ {149,176,185}` on physical digits. -/
theorem reverseCrossCode_ge_sharp_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) :
    ∀ N : Nat,
      1 ≤ N →
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
      94 * (((4^N : Nat) : Int)) + sharpTerminalPotential (d N) ≤
        5 * reverseCrossCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd hout
      by_cases hN0 : N = 0
      · subst N
        have hpres :=
          happyCell_positive_and_preserves_big2 (C 0) (d 0) hfirst
        have hout0 := hout 0 (by omega)
        have hd1 : d 1 = 2 := by
          calc
            d 1 = outDigit (C 0) (d 0) := by simpa using hout0.symm
            _ = 2 := hpres.2
        rw [reverseCrossCode]
        simp only [reverseCrossCode]
        rw [crossDensity_happy_exact (C 0) (d 0) hfirst, hd1]
        norm_num [sharpTerminalPotential]
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' :
            94 * (((4^N : Nat) : Int)) + sharpTerminalPotential (d N) ≤
              5 * reverseCrossCode C d N :=
          ih hNpos
            (fun t ht => hC t (by omega))
            (fun t ht => hd t (by omega))
            (fun t ht => hout t (by omega))
        have hlocal := sharpTerminalPotential_step
          (C N) (d N) (hC N (by omega)) (hd N (by omega))
        have houtN := hout N (by omega)
        have hpowCast :
            (((4^(N+1) : Nat) : Int)) =
              4 * (((4^N : Nat) : Int)) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        rw [reverseCrossCode]
        change
          94 * (((4^(N+1) : Nat) : Int)) +
              sharpTerminalPotential (d (N+1)) ≤
            5 * (4 * reverseCrossCode C d N + crossDensity (C N) (d N))
        rw [hpowCast, ← houtN]
        omega

#check sharpTerminalPotential_step
#check reverseCrossCode_ge_sharp_of_leading_happy
#print axioms sharpTerminalPotential_step
#print axioms reverseCrossCode_ge_sharp_of_leading_happy

end GSTU2DExactCrossingCharge