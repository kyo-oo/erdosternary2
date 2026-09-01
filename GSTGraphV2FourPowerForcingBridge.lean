import GSTFourPowerOntologicalAdapter
import GSTGraphV2CanonicalNWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2FourPowerForcingBridge

open GSTCanonicalTailStateIso
open GSTFourPowerOntologicalAdapter
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalNWave
open GSTGraphV2HandwrittenExponentialCascade

/-- Literal Graph-V2 form of the remaining four-power forcing law.  This is
the exact theorem that must replace the quarantined recursive creation block:
every relevant power sheet contains a physical Happy cell above row zero. -/
def FourPowerGraphForcing : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ∃ p : Nat, 1 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p)

/-- Exact one-trit regeneration observed on Graph V2.  The information wave
does regenerate at the next canonical scale, but its consumed origin trit is
retained as a horizontal phase.  This is the non-lossy form needed for
iteration; no invalid reset of the phase to column zero is performed. -/
theorem one_trit_phase_regeneration_happy_iff
    (s n x p : Nat) :
    GSTU2DEventTransport.HappyCell
        (graph (canonicalEnergy s n) x p).seven.carry
        (graph (canonicalEnergy s n) x p).seven.digit ↔
      GSTU2DEventTransport.HappyCell
        (graph (canonicalEnergy (s+1) (n/3))
          (3^(s+1) * (n%3) + x) p).seven.carry
        (graph (canonicalEnergy (s+1) (n/3))
          (3^(s+1) * (n%3) + x) p).seven.digit := by
  simpa [nWaveEnergy, nWaveShift, uTailEnergy, uTailExponent,
    uPhaseShift, originPrefix, originSuffix, canonicalEnergy,
    Nat.add_assoc] using
      (canonical_n_wave_happy_iff s n 1 x p)

/-- A physical Happy cell gives the historical creation certificate directly;
the information is retained in the carry-zero/carry-three realization. -/
theorem graph_forcing_to_creation_master
    (hGraph : FourPowerGraphForcing) :
    FourPowerCreationMaster := by
  intro K hK5 hK7
  obtain ⟨p, hp, hd, hC⟩ := hGraph K hK5 hK7
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [digit3] using hd
  · left
    change carry4 (4^K) p % 3 = 0
    rcases hC with h0 | h3
    · simp [h0]
    · simp [h3]

/-- Conversely, the creation master produces a physical Graph-V2 Happy cell.
This proves that the graph law is not a stronger replacement assumption: it
is exactly the old master expressed on the actual spacetime sheet. -/
theorem creation_master_to_graph_forcing
    (hMaster : FourPowerCreationMaster) :
    FourPowerGraphForcing := by
  intro K hK5 hK7
  obtain ⟨p, hd, hC⟩ :=
    creation_certificate_to_navigation (4^K) (hMaster K hK5 hK7)
  have hp : 1 ≤ p := by
    cases p with
    | zero =>
        simp [digit3, Nat.pow_mod] at hd
    | succ p => omega
  exact ⟨p, hp, hd, hC⟩

theorem graph_forcing_iff_creation_master :
    FourPowerGraphForcing ↔ FourPowerCreationMaster := by
  exact ⟨graph_forcing_to_creation_master,
    creation_master_to_graph_forcing⟩

#check graph_forcing_to_creation_master
#check creation_master_to_graph_forcing
#check one_trit_phase_regeneration_happy_iff
#print axioms graph_forcing_iff_creation_master

end GSTGraphV2FourPowerForcingBridge
