import GSTGraphV2FourPowerRelocation
import GSTGraphV2PerfectPowerAncestry
import GSTGraphV2SixAdicSynchronizedShadows
import GSTFourPowerDirectFailedRelocationState

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerThirdWave

open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicSynchronizedShadows
open GSTFourPowerDirectExistence
open GSTFourPowerDirectFailedRelocationState

/-- The physical cell on wave u of the four-power third-wave packet. -/
def waveCell (K u p : Nat) :=
  graph 1 (K + u) p

/-- Integer energy chart carried by wave u. -/
def waveEnergy (K u : Nat) : Int :=
  (4 : Int)^(K + u)

/-- A genuine width-three obstruction packet in the existing Graph-V2 universe:
a Happy child on the left endpoint and complete badness on the right endpoint. -/
structure WidthThreeBadPacket (K q : Nat) : Prop where
  childHappy :
    HappyCell (waveCell K 0 q).seven.carry (waveCell K 0 q).seven.digit
  rightBad :
    ∀ j : Nat,
      ¬ HappyCell (waveCell K 3 j).seven.carry (waveCell K 3 j).seven.digit

/-- The same width-three packet on the literal 4^K-energy rectangle. -/
theorem widthThreeBadPacket_graph_realization
    {K q : Nat} (h : WidthThreeBadPacket K q) :
    HappyCell
        (graph (4^K) 0 q).seven.carry
        (graph (4^K) 0 q).seven.digit ∧
      ∀ j : Nat,
        ¬ HappyCell
          (graph (4^K) 3 j).seven.carry
          (graph (4^K) 3 j).seven.digit := by
  constructor
  · have hiff := power_origin_happy_iff K 0 q
    apply hiff.mpr
    simpa [waveCell] using h.childHappy
  · intro j hRight
    apply h.rightBad j
    have hiff := power_origin_happy_iff K 3 j
    have habs := hiff.mp hRight
    simpa [waveCell, Nat.add_assoc] using habs

/-- Exact endpoint factorization of the third wave. -/
theorem waveEnergy_three_factor (K : Nat) :
    waveEnergy K 3 = (4 : Int)^K * 64 := by
  simp [waveEnergy, pow_add]
  ring

/-- The left endpoint is the same physical chart with unit residual factor. -/
theorem waveEnergy_zero_factor (K : Nat) :
    waveEnergy K 0 = (4 : Int)^K * 1 := by
  simp [waveEnergy]

/-- Width three has exactly two synchronized six-adic levels:
4^(K+3)-4^K = 63*4^K, and for K>=1 this is divisible by 6^2. -/
theorem third_wave_six_adic_iso_two
    (K : Nat) (hK : 1 ≤ K) :
    SixAdicIsoAt 2 (waveEnergy K 3) (waveEnergy K 0) := by
  rw [waveEnergy_three_factor, waveEnergy_zero_factor]
  apply (six_iso_mul_four_pow_iff_truncated_skew_shadows 2 K 64 1).2
  constructor
  · have hsub : 2 - 2*K = 0 := by omega
    rw [hsub]
    exact dyadic_shadow_zero 64 1
  · refine ⟨7, ?_⟩
    norm_num [TriadicShadowAt]

/-- The same width-three endpoints split at six-adic resolution three.
The obstruction is already triadic: 64-1=63 is divisible by 3^2 but not 3^3. -/
theorem third_wave_not_six_adic_iso_three
    (K : Nat) :
    ¬ SixAdicIsoAt 3 (waveEnergy K 3) (waveEnergy K 0) := by
  intro hSix
  have hTri :
      TriadicShadowAt 3 (waveEnergy K 3) (waveEnergy K 0) :=
    (six_iso_iff_synchronized_shadows.mp hSix).2
  rw [waveEnergy_three_factor, waveEnergy_zero_factor] at hTri
  have hBase : TriadicShadowAt 3 (64 : Int) 1 :=
    (triadic_shadow_mul_four_pow_iff 3 K 64 1).1 hTri
  rcases hBase with ⟨z, hz⟩
  norm_num at hz
  omega

/-- Boxed ontological signature of the newly exposed third wave. -/
theorem third_wave_resolution_split
    (K : Nat) (hK : 1 ≤ K) :
    SixAdicIsoAt 2 (waveEnergy K 3) (waveEnergy K 0) ∧
      ¬ SixAdicIsoAt 3 (waveEnergy K 3) (waveEnergy K 0) :=
  ⟨third_wave_six_adic_iso_two K hK,
    third_wave_not_six_adic_iso_three K⟩

/-- A failed one-step relocation produces a deterministic three-wave physical
packet on the middle sheet.  This is the local seed that will be inserted into
the width-three resolution split. -/
structure FailedRelocationThirdWaveState (K : Nat) : Prop where
  q : Nat
  q_ge_two : 2 ≤ q
  carry_three :
    GSTFourPowerDirectAdditionCarry.directCarry4 (4^(K+1)) q = 3
  middle_equal :
    GSTFourPowerDirectResidue.digit3 (4^(K+1)) q =
      GSTFourPowerDirectResidue.digit3 (4^(K+2)) q
  middle_non_two :
    GSTFourPowerDirectResidue.digit3 (4^(K+1)) q < 2
  next_binary_one :
    GSTFourPowerDirectAdditionCarry.binaryCarry (4^(K+1)) (q+1) = 1
  next_carry_middle :
    GSTFourPowerDirectAdditionCarry.directCarry4 (4^(K+1)) (q+1) = 1 ∨
      GSTFourPowerDirectAdditionCarry.directCarry4 (4^(K+1)) (q+1) = 2

/-- Existing exact direct arithmetic manufactures the third-wave state from
a source overlap plus failure of the next overlap. -/
theorem failed_relocation_to_third_wave_state
    (K : Nat) (hCommon : CommonTwo K) (hNoNext : ¬ CommonTwo (K+1)) :
    FailedRelocationThirdWaveState K := by
  obtain ⟨q, hq, hC3, hEq, hlt, hb1, hnext⟩ :=
    commonTwo_failed_relocation_two_step_physical_state K hCommon hNoNext
  exact ⟨q, hq, hC3, hEq, hlt, hb1, hnext⟩

#check waveCell
#check waveEnergy
#check WidthThreeBadPacket
#check widthThreeBadPacket_graph_realization
#check third_wave_six_adic_iso_two
#check third_wave_not_six_adic_iso_three
#check third_wave_resolution_split
#check FailedRelocationThirdWaveState
#check failed_relocation_to_third_wave_state
#print axioms widthThreeBadPacket_graph_realization
#print axioms third_wave_resolution_split
#print axioms failed_relocation_to_third_wave_state

end GSTGraphV2FourPowerThirdWave
