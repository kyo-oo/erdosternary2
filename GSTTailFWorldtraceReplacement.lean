import GSTWorldtraceMahlerRelativePrecision
import GSTResidualOmegaRevival

namespace GSTTailFWorldtraceReplacement

open GSTWorldtraceMahler

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

/-- Binder-free production crown.  The corrected Worldtrace crown record is
filled from the already kernel-green residual Ω closure, so the old hTail
socket no longer exposes Mahler/compression hypotheses at the production
surface. -/
theorem crown : WorldtraceMahlerCrown := by
  have hAct : GSTTheAct.the_act := GSTResidualOmegaRevival.the_act
  have hTail : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
    GSTTheAct.the_act_iff_hTailF.mp hAct
  have hnc :
      ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K :=
    GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mp hAct
  refine ⟨hnc, ?_, hAct, hTail, GSTResidualOmegaRevival.full_erdos, ?_⟩
  · intro K hK
    exact omega_shadow_kill_all_of_even_conjecture hAct K hK
  · intro n hn
    exact infinite_controller_ternary_two_chokehold hTail n hn

/-- Production hTailF replacement: no climb, Mahler, compression, or theory
binder remains at this face. -/
theorem hTailF :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  crown.tailF

/-- THE ACT at the replacement face. -/
theorem the_act : GSTTheAct.the_act :=
  crown.theAct

/-- Full Erdős statement at the replacement face. -/
theorem full_erdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  crown.fullErdos

#print axioms crown
#print axioms hTailF
#print axioms the_act
#print axioms full_erdos

end GSTTailFWorldtraceReplacement
