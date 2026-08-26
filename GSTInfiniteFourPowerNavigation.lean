import GSTFinalPurePowerResidueTransplant
import GSTGraphV2ProductionLaws

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenExponentialLTE
open GSTFinalPurePowerResidueTransplant

/-!
# Universal four-power Navigation

Standalone exact-#501 proof surface.  This file deliberately imports only
kernel-green modules from the Aug-19--24 stack.  The public theorem will keep
the old universal `(k, hk5, hk7)` contract and will not depend on the
prefix-one theorem or the broken legacy recursive `h_creation_for_4pow`.
-/

#check digit3
#check carry4
#check GSTFinalPurePowerResidueTransplant.wideCarry
#check GSTFinalPurePowerResidueTransplant.wideDigit
#check GSTFinalPurePowerResidueTransplant.wideCarry_forward_exact
#check GSTFinalPurePowerResidueTransplant.stripConservation_exact
#check GSTFinalPurePowerResidueTransplant.pow4_mod3_one
#check GSTFinalPurePowerResidueTransplant.pow4_exponent_trit_lift_digit
#check GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_mod_next
#check GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_cut_carry_zero
#check GSTGraphV2HandwrittenExponentialLTE.pow4_scaled_cut_digit_zero
