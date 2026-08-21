import ErdosPreOmega
import GSTGraphV2SleepEquationLabScratch
import GSTGraphV2SleepEquationCollisionScratch
import GSTGraphV2InfiniteBigNDichotomyScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Handwritten equation -> live prefix-one production probe

Literal page, as recovered by the Aug-20 transcription:

  Π_{t→∞}^{n≠0} { ∫_{∞}^{-∞} (lim_{j→∞} e^x) }
    2^j ∪ 3^j ∪ 6^j - f_m ∪ Σ_{S≠0}^{S≠3^x} S n^x

This probe does not assign a new meaning to the unresolved `f_m` glyph.
The first theorem checks the important production fact: the already-kernelized
Π/U/Ω/2-3-6/S operator attaches to the *actual* Navigation child used by the
prefix-one collision, rather than to an unrelated laboratory integer.
-/

theorem gpt56_handwritten_operator_on_navigation_child
    (s n : Nat) (hs : 1 ≤ s) :
    GSTSleepFullOperatorS
      (s+1) n (gstNavigationConstant (s+1) n) := by
  apply gst_sleep_full_operatorS
  unfold GSTSleepNavigationEnergyCouplingS
  unfold gstOmegaPressureEnergyS gstOriginRemainingUS
  exact (gst_navigation_decomposition (s+1) n (by omega)).symm

#check gpt56_handwritten_operator_on_navigation_child
#print axioms gpt56_handwritten_operator_on_navigation_child
