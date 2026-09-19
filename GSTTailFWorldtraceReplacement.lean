import GSTWorldtraceMahlerRelativePrecision

namespace GSTTailFWorldtraceReplacement

open GSTWorldtraceMahler

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

/-- Production crown sourced from the corrected Worldtrace–Mahler terminal
interface.  This is the replacement provider above the old GST hTail socket. -/
theorem crown
    (H : MahlerSharp) (HC : ResidualGhostCompression) :
    WorldtraceMahlerCrown :=
  worldtrace_mahler_crown_of_residual_ghost H HC

/-- Production hTailF provider.  The old climb/no-Cantorian socket is no
longer needed at the monolith entry face; the green Worldtrace crown already
contains the exact hTailF object. -/
theorem hTailF
    (H : MahlerSharp) (HC : ResidualGhostCompression) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  (crown H HC).tailF

/-- The same replacement crown read at THE ACT face. -/
theorem the_act
    (H : MahlerSharp) (HC : ResidualGhostCompression) :
    GSTTheAct.the_act :=
  (crown H HC).theAct

/-- The same replacement crown read at the full Erdős face. -/
theorem full_erdos
    (H : MahlerSharp) (HC : ResidualGhostCompression) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  (crown H HC).fullErdos

#print axioms crown
#print axioms hTailF
#print axioms the_act
#print axioms full_erdos

end GSTTailFWorldtraceReplacement
