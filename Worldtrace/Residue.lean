import ErdosTernary2
import Worldtrace.Genesis
import GST.FourPower.PrefixLaw

/-!
# Worldtrace residue tower layer

Public names for the stable low-residue fingerprints and exponent-prefix
obstructions.  This layer is where local modular data becomes persistent
worldtrace information rather than isolated congruence arithmetic.
-/

namespace Worldtrace
namespace Residue

/-- The cascade constant whose stable residues drive the early bridge. -/
abbrev CascadeConstant : Nat → Nat := Worldtrace.Genesis.CascadeConstant

/-- Stable cascade residue at precision `3^k`. -/
abbrev StableCascadeConstant : Nat → Nat := Worldtrace.Genesis.StableCascadeConstant

/-- Low ternary prefix of the exponent below scale `3^p`. -/
abbrev exponentPrefix : Nat → Nat → Nat := GST.FourPower.exponentPrefix

/-- The `p`-th ternary trit of the exponent. -/
abbrev exponentTrit : Nat → Nat → Nat := GST.FourPower.exponentTrit

/-- Mod-three cascade fingerprint. -/
abbrev cascade_mod_three := Worldtrace.Genesis.cascade_mod_three

/-- Mod-nine cascade fingerprint. -/
abbrev cascade_mod_nine := Worldtrace.Genesis.cascade_mod_nine

/-- Stable mod-three residue of the cascade constant. -/
abbrev stable_cascade_mod_three := Worldtrace.Genesis.stable_cascade_mod_three

/-- Stable mod-nine residue of the cascade constant. -/
abbrev stable_cascade_mod_nine := Worldtrace.Genesis.stable_cascade_mod_nine

/-- Stable mod-eighty-one residue of the cascade constant. -/
abbrev cascade_mod_eighty_one_stable := Worldtrace.Genesis.cascade_mod_eighty_one_stable

/-- Stable mod-two-hundred-forty-three residue of the cascade constant. -/
abbrev cascade_mod_two_four_three_stable := Worldtrace.Genesis.cascade_mod_two_four_three_stable

/-- Exact decomposition of an exponent into prefix, trit, and suffix. -/
abbrev exponent_prefix_trit_decomposition := GST.FourPower.exponent_prefix_trit_decomposition

/-- Pair formula for consecutive powers of four from one exponent trit. -/
abbrev pow4_pair_from_exponent_trit := GST.FourPower.pow4_pair_from_exponent_trit

/-- Parametric obstruction for a common-two-free exponent trit. -/
abbrev no_common_two_exponent_trit_obstruction := GST.FourPower.no_common_two_exponent_trit_obstruction

end Residue
end Worldtrace
