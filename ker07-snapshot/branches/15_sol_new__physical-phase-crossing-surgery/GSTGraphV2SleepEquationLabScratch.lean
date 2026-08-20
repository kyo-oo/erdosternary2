import GSTGraphV2InfiniteElevenEquationMasterScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Full handwritten sleep-operator laboratory

Correction to the first transcription: the glyph at the right is `S`, not the
number five.  We therefore do NOT identify the handwritten Sigma term with the
old `55...55_6` geometric word.

The source meanings are kept:

* Pi / t-axis: all-scale natural-origin constructor;
* U: simultaneous multiply/divide conservation;
* Omega-infinity: Nat-indexed information transfer with controlled total;
* 2^j, 3^j, 6^j: the binary / ternary / mixed world scales;
* S: the GST physical space coordinate.

For the seven-axis / three-space graph we encode S by the exact signed charge
used by the old U-space calculation:

  GST+ -> +4,   NULL/ALT- -> -1.

The visible handwritten term `S n^x` is tested as the weighted space moment of
the five exact local U-readings.  The corresponding microscopic energy/mass
moment is retained as the `e^x` channel.  Evaluating both channels in the
2-world, 3-world and 6-world gives a complete fingerprint of every legal GST
cell.
-/

/-- Exact local GST re-coordinate map. -/
def gstSleepRotateS (x : Nat × Nat) : Nat × Nat :=
  ((x.1 + 4*x.2) / 3, (x.1 + 4*x.2) % 3)

/-- S is the signed three-space coordinate, not the numeral 5. -/
def gstSleepSChargeS (C : Nat) : Int :=
  if C = 3 then 4 else -1

/-- Microscopic event-energy/mass coordinate of one GST cell. -/
def gstSleepEnergyS (C d : Nat) : Int := (C + 4*d : Nat)

/-- Five-reading weighted S-sum: the literal `sum S*n^x` interpretation. -/
def gstSleepSMomentS (C d : Nat) (n : Int) : Int :=
  let x0 : Nat × Nat := (C,d)
  let x1 := gstSleepRotateS x0
  let x2 := gstSleepRotateS x1
  let x3 := gstSleepRotateS x2
  let x4 := gstSleepRotateS x3
  gstSleepSChargeS x0.1 * n^0 +
  gstSleepSChargeS x1.1 * n^1 +
  gstSleepSChargeS x2.1 * n^2 +
  gstSleepSChargeS x3.1 * n^3 +
  gstSleepSChargeS x4.1 * n^4

/-- Matching five-reading microscopic energy/event moment. -/
def gstSleepEMomentS (C d : Nat) (n : Int) : Int :=
  let x0 : Nat × Nat := (C,d)
  let x1 := gstSleepRotateS x0
  let x2 := gstSleepRotateS x1
  let x3 := gstSleepRotateS x2
  let x4 := gstSleepRotateS x3
  gstSleepEnergyS x0.1 x0.2 * n^0 +
  gstSleepEnergyS x1.1 x1.2 * n^1 +
  gstSleepEnergyS x2.1 x2.2 * n^2 +
  gstSleepEnergyS x3.1 x3.2 * n^3 +
  gstSleepEnergyS x4.1 x4.2 * n^4

/-- The three handwritten radix worlds still join exactly at every depth. -/
theorem gst_sleep_three_world_joinS (j : Nat) :
    2^j * 3^j = 6^j := by
  have h := Nat.mul_pow 2 3 j
  norm_num at h
  exact h.symm

/-- U-neutrality is recovered by evaluating the S Sigma at n=1. -/
theorem gst_sleep_nonfixed_S_sigma_U_neutralS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hnot0 : (C,d) ≠ (0,0))
    (hnotPlus : (C,d) ≠ (3,2)) :
    gstSleepSMomentS C d 1 = 0 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [gstSleepSMomentS, gstSleepRotateS, gstSleepSChargeS] at hnot0 hnotPlus ⊢

/-- Exact phase law for the weighted S Sigma under one local U re-reading.
For a legal five-cycle, rotating the starting cell multiplies the moment by n
up to the boundary term S_0*(n^5-1). -/
theorem gst_sleep_S_sigma_rotation_lawS
    (C d : Nat) (hC : C < 4) (hd : d < 3) (n : Int) :
    let y := gstSleepRotateS (C,d)
    n * gstSleepSMomentS y.1 y.2 n =
      gstSleepSMomentS C d n + gstSleepSChargeS C * (n^5 - 1) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    simp [gstSleepSMomentS, gstSleepRotateS, gstSleepSChargeS]

/-- Full 2/3/6 readout of the handwritten S/e channels. -/
structure GSTSleepThreeWorldFingerprintS where
  S2 : Int
  S3 : Int
  S6 : Int
  E2 : Int
  E3 : Int
  E6 : Int
  deriving Repr, DecidableEq

def gstSleepThreeWorldFingerprintS (C d : Nat) :
    GSTSleepThreeWorldFingerprintS where
  S2 := gstSleepSMomentS C d 2
  S3 := gstSleepSMomentS C d 3
  S6 := gstSleepSMomentS C d 6
  E2 := gstSleepEMomentS C d 2
  E3 := gstSleepEMomentS C d 3
  E6 := gstSleepEMomentS C d 6

/-- Main experimental result: the whole 2/3/6 + S*n^x + e^x readout is a
complete local state coordinate.  No two legal carry/digit cells share it. -/
theorem gst_sleep_three_world_fingerprint_injectiveS
    (C d C' d' : Nat)
    (hC : C < 4) (hd : d < 3)
    (hC' : C' < 4) (hd' : d' < 3)
    (hfp : gstSleepThreeWorldFingerprintS C d =
      gstSleepThreeWorldFingerprintS C' d') :
    C = C' ∧ d = d' := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  have hCc' : C' = 0 ∨ C' = 1 ∨ C' = 2 ∨ C' = 3 := by omega
  have hdc' : d' = 0 ∨ d' = 1 ∨ d' = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3
  all_goals rcases hdc with d0 | d1 | d2
  all_goals rcases hCc' with h0' | h1' | h2' | h3'
  all_goals rcases hdc' with d0' | d1' | d2'
  all_goals subst_vars
  all_goals norm_num [gstSleepThreeWorldFingerprintS, gstSleepSMomentS,
    gstSleepEMomentS, gstSleepRotateS, gstSleepSChargeS,
    gstSleepEnergyS] at hfp ⊢

/-- The two Happy-Gate cells have two distinguished whole-equation
fingerprints; injectivity makes this an algebraic gate detector. -/
def GSTSleepHappyFingerprintS (F : GSTSleepThreeWorldFingerprintS) : Prop :=
  F = gstSleepThreeWorldFingerprintS 0 2 ∨
  F = gstSleepThreeWorldFingerprintS 3 2

theorem gst_sleep_happy_iff_three_world_fingerprintS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    GSTHappyPairS C d ↔
      GSTSleepHappyFingerprintS (gstSleepThreeWorldFingerprintS C d) := by
  constructor
  · rintro ⟨rfl, rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro h
    rcases h with h0 | h3
    · have hEq := gst_sleep_three_world_fingerprint_injectiveS
        C d 0 2 hC hd (by decide) (by decide) h0
      exact ⟨hEq.2, Or.inl hEq.1⟩
    · have hEq := gst_sleep_three_world_fingerprint_injectiveS
        C d 3 2 hC hd (by decide) (by decide) h3
      exact ⟨hEq.2, Or.inr hEq.1⟩

/-- Coupling equation between the Pi-origin energy and the BIG-N Omega energy.
For a canonical Navigation constant this is exactly the usual decomposition. -/
def GSTSleepNavigationEnergyCouplingS (t n N : Nat) : Prop :=
  gstOmegaPressureEnergyS t N = gstOriginRemainingUS t n

/-- Full whole-expression package.  Pi is all-scale, U is all-scale, Omega is
an actual Nat-indexed controlled infinite stream, and the S/e Sigma readout in
the 2/3/6 worlds is a complete microscopic coordinate. -/
structure GSTSleepFullOperatorS (t n N : Nat) : Prop where
  energyCoupling : GSTSleepNavigationEnergyCouplingS t n N
  omegaInfinite :
    GSTControlledInfiniteSumS
      (gstOmegaNaturalTransferS t N) (3^(t+1) * N)
  piUInfinite : GSTOriginInfiniteMulDivControlS t n
  omegaClosesToPi : gstOmegaPressureEnergyS t N = gstOriginRemainingUS t n
  threeWorldJoin : ∀ j : Nat, 2^j * 3^j = 6^j
  SphaseLaw : ∀ C d : Nat, C < 4 → d < 3 → ∀ b : Int,
    let y := gstSleepRotateS (C,d)
    b * gstSleepSMomentS y.1 y.2 b =
      gstSleepSMomentS C d b + gstSleepSChargeS C * (b^5 - 1)
  fingerprintComplete : ∀ C d C' d' : Nat,
    C < 4 → d < 3 → C' < 4 → d' < 3 →
    gstSleepThreeWorldFingerprintS C d =
      gstSleepThreeWorldFingerprintS C' d' →
    C = C' ∧ d = d'

/-- The complete equation is internally consistent whenever the Navigation
energy coupling holds.  Nothing here substitutes a finite cutoff for infinity. -/
theorem gst_sleep_full_operatorS
    (t n N : Nat)
    (hlink : GSTSleepNavigationEnergyCouplingS t n N) :
    GSTSleepFullOperatorS t n N := by
  refine {
    energyCoupling := hlink
    omegaInfinite := gst_omega_natural_transfer_infinite_controlS t N
    piUInfinite := gst_origin_infinite_mul_div_controlS t n
    omegaClosesToPi := hlink
    threeWorldJoin := ?_
    SphaseLaw := ?_
    fingerprintComplete := ?_ }
  · intro j
    exact gst_sleep_three_world_joinS j
  · intro C d hC hd b
    exact gst_sleep_S_sigma_rotation_lawS C d hC hd b
  · intro C d C' d' hC hd hC' hd' hfp
    exact gst_sleep_three_world_fingerprint_injectiveS
      C d C' d' hC hd hC' hd' hfp

#check gst_sleep_three_world_joinS
#check gst_sleep_nonfixed_S_sigma_U_neutralS
#check gst_sleep_S_sigma_rotation_lawS
#check gst_sleep_three_world_fingerprint_injectiveS
#check gst_sleep_happy_iff_three_world_fingerprintS
#check gst_sleep_full_operatorS

#print axioms gst_sleep_three_world_fingerprint_injectiveS
#print axioms gst_sleep_full_operatorS

end GSTInfiniteV2
