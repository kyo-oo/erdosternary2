import GSTFourPowerExponentTritObstruction

/-!
# Exponent-prefix API

Public names for the parametric exponent-prefix law. These wrappers expose the
clean mathematical surface while preserving the internal proof artifact.
-/

namespace GST
namespace FourPower

/-- Low ternary prefix of the exponent below scale `3^p`. -/
abbrev exponentPrefix : Nat → Nat → Nat := GSTFourPowerExponentTritObstruction.exponentPrefix

/-- The `p`-th ternary trit of the exponent. -/
abbrev exponentTrit : Nat → Nat → Nat := GSTFourPowerExponentTritObstruction.exponentTrit

/-- Exact decomposition of an exponent into low prefix, current trit, and high suffix. -/
theorem exponent_prefix_trit_decomposition (K p : Nat) :
    K = exponentPrefix K p
      + exponentTrit K p * 3^p
      + 3^(p+1) * ((K / 3^p) / 3) := by
  exact GSTFourPowerExponentTritObstruction.exponent_prefix_trit_decomposition K p

/-- Exact pair formula: the exponent trit shifts both consecutive-power row values. -/
theorem pow4_pair_from_exponent_trit (K p : Nat) :
    GSTFourPowerDirectResidue.digit3 (4^K) (p+1) =
        (GSTFourPowerDirectResidue.digit3 (4^(exponentPrefix K p)) (p+1) + exponentTrit K p) % 3
      ∧
    GSTFourPowerDirectResidue.digit3 (4^(K+1)) (p+1) =
        (GSTFourPowerDirectResidue.digit3 (4^((exponentPrefix K p)+1)) (p+1) + exponentTrit K p) % 3 := by
  exact GSTFourPowerExponentTritObstruction.pow4_pair_from_exponent_trit K p

/-- Parametric direct obstruction on every ternary exponent trit. -/
theorem no_common_two_exponent_trit_obstruction
    (K p : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      GSTFourPowerDirectResidue.digit3 (4^K) q = 2 ∧
      GSTFourPowerDirectResidue.digit3 (4^(K+1)) q = 2)
    (heq :
      GSTFourPowerDirectResidue.digit3 (4^(exponentPrefix K p)) (p+1) =
      GSTFourPowerDirectResidue.digit3 (4^((exponentPrefix K p)+1)) (p+1)) :
    exponentTrit K p ≠
      2 - GSTFourPowerDirectResidue.digit3 (4^(exponentPrefix K p)) (p+1) := by
  exact GSTFourPowerExponentTritObstruction.no_common_two_exponent_trit_obstruction K p hNo heq

end FourPower
end GST
