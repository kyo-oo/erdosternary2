import GSTWorldtraceMahlerRelativePrecision

namespace GSTTailFWorldtraceReplacement

open GSTWorldtraceMahler

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

/-!
# Zero-input Worldtrace production replacement

The former production surface accepted external terminal proof sockets.
This module removes that interface entirely.

The live monolith already contains the unconditional even theorem
`erdos_ternary_2_even_universal`; the odd wing is elementary.  From those
kernel theorems we reconstruct THE ACT, the no-Cantorian face, hTailF, the
full Erdős statement, and the existing crown with no custom hypothesis.
-/

/-- Every even half-exponent in the theorem range contains a ternary two. -/
theorem even_erdos :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false := by
  intro K hK
  exact has_two_imp_not_no_two (4^K)
    (erdos_ternary_2_even_universal K (by omega))

/-- Binder-free THE ACT. -/
theorem the_act : GSTTheAct.the_act := by
  intro K hK
  exact even_erdos K hK

/-- The Cantorian obstruction is empty, with no external premise. -/
theorem no_cantorian :
    ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K :=
  GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mp the_act

/-- Binder-free terminal tail face. -/
theorem hTailF :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF.mp the_act

/-- Binder-free full Erdős ternary-2 statement. -/
theorem full_erdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTTheAct.full_erdos_of_the_act the_act

/-- Explicit digit-two witness form of THE ACT. -/
theorem kill_all :
    ∀ K : Nat, 8 ≤ K → ∃ p : Nat,
      GSTCanonicalSevenAxisBridge.digit3 (4^K) p = 2 := by
  intro K hK
  obtain ⟨p, hp⟩ := omega_shadow_kill_all_of_even_conjecture the_act K hK
  exact ⟨p, hp⟩

/-- Zero-input production crown. -/
theorem crown : WorldtraceMahlerCrown := by
  refine ⟨no_cantorian, kill_all, the_act, hTailF, full_erdos, ?_⟩
  intro n hn
  exact infinite_controller_ternary_two_chokehold hTailF n hn

#print axioms even_erdos
#print axioms the_act
#print axioms no_cantorian
#print axioms hTailF
#print axioms full_erdos
#print axioms crown

end GSTTailFWorldtraceReplacement
