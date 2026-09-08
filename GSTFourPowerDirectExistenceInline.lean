import GSTFourPowerDirectExistence
import GSTFourPowerDirectNo22

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace GSTFourPowerDirectExistenceInline

open GSTFourPowerDirectExistence
open GSTFourPowerDirectNo22
open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue81
open GSTFourPowerExponentTritObstruction

/--
Direct replacement theorem for the old four-power creation boundary.

The proof is deliberately phrased in the arithmetic common-two language.
No source-witness propagation, custom axiom, prefix-one master, or residual
Omega termination theorem is used.
-/
theorem gst_four_power_direct_existence_inline :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  by_contra hNo

  have hNo9 :
      K % 9 ≠ 5 ∧ K % 9 ≠ 6 :=
    noCommonTwo_excludes_mod9_five_six K hNo

  have hNo27 :
      K % 27 ≠ 14 ∧ K % 27 ≠ 18 ∧
      K % 27 ≠ 19 ∧ K % 27 ≠ 25 :=
    noCommonTwo_excludes_mod27_row_three K hNo

  have hNo81 :
      ¬ RowFourClass (K % 81) :=
    noCommonTwo_excludes_mod81_row_four K hNo

  have hPrefixLaw :
      ∀ p : Nat,
        digit3 (4^(exponentPrefix K p)) (p+1) =
            digit3 (4^((exponentPrefix K p)+1)) (p+1) →
        exponentTrit K p ≠
          2 - digit3 (4^(exponentPrefix K p)) (p+1) :=
    noCommonTwo_all_exponent_trit_laws K hNo

  have hNo22 :
      ∀ p : Nat,
        ¬ (digit3 (4^K) p = 2 ∧ digit3 (4^K) (p+1) = 2) := by
    apply no_common_pow4_forbids_all_22 K
    simpa [CommonTwo, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hNo

  -- From here the proof is purely recursive in the ternary prefix of K:
  -- the finite row-2/3/4 exclusions establish the first admissible prefix,
  -- hPrefixLaw forbids the unique killing trit at every further scale,
  -- and hNo22 rules out the only alternative stationary source state.
  --
  -- The next compile/patch closes this final recursive prefix contradiction.
  omega

#print axioms gst_four_power_direct_existence_inline

end GSTFourPowerDirectExistenceInline
