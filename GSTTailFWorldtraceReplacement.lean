import GSTResidualOmegaRevival
import GSTWorldtraceMahlerRelativePrecision

namespace GSTTailFWorldtraceReplacement

open GSTWorldtraceMahler

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

/-- Binder-free THE ACT, supplied by the kernel-green residual Omega closure. -/
theorem the_act : GSTTheAct.the_act :=
  GSTResidualOmegaRevival.the_act

/-- Production hTailF replacement.  This is the exact old hTail socket,
now discharged by the binder-free residual theorem rather than the legacy
climb/provider premise. -/
theorem hTailF :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF.mp the_act

/-- Binder-free full Erdős theorem from the same replacement provider. -/
theorem full_erdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTResidualOmegaRevival.full_erdos

/-- Cantorian extinction read from the now-closed ACT face. -/
theorem no_cantorian :
    ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K :=
  GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mp the_act

/-- Explicit digit-two witness form of the closed ACT face. -/
theorem kill_all :
    ∀ K : Nat, 8 ≤ K → ∃ p : Nat,
      GSTCanonicalSevenAxisBridge.digit3 (4^K) p = 2 := by
  intro K hK
  obtain ⟨p, hp⟩ := no_two_false_digit_witness (4^K) (the_act K hK)
  exact ⟨p, by
    simpa [GSTCanonicalSevenAxisBridge.digit3] using hp⟩

/-- Zero-input production crown.  This preserves the Worldtrace terminal
interface while sourcing every terminal face from the repaired residual proof. -/
theorem crown : WorldtraceMahlerCrown := by
  refine ⟨no_cantorian, kill_all, the_act, hTailF, full_erdos, ?_⟩
  intro n hn
  exact infinite_controller_ternary_two_chokehold hTailF n hn

#print axioms the_act
#print axioms hTailF
#print axioms full_erdos
#print axioms no_cantorian
#print axioms kill_all
#print axioms crown

end GSTTailFWorldtraceReplacement
