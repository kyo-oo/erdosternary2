import ErdosTernary2

/-!
# Worldtrace genesis layer

Public names for the original arithmetic engine in the first stretch of the
monolith.  This is the True Duality Transcendence / cascade layer: ternary
worlds, the cascade constant, structural computation, and the bridge identities
that later feed navigation and collision theory.

The declarations here are wrappers only.  They preserve the checked proof corpus
and give the early 0--6k monolith machinery a stable Worldtrace-facing surface.
-/

namespace Worldtrace
namespace Genesis

/-- The cascade constant appearing in the low-tower identity. -/
abbrev CascadeConstant : Nat → Nat := _root_.c

/-- Stable low residue of the cascade constant at precision `3^k`. -/
abbrev StableCascadeConstant : Nat → Nat := _root_.c_stable

/-- Structural modular exponentiation used by kernel-decidable checks. -/
abbrev powMod : Nat → Nat → Nat → Nat := _root_.powMod

/-- Correctness of structural modular exponentiation. -/
abbrev pow_mod_eq := _root_.powMod_eq

/-- Strengthened correctness form for structural modular exponentiation. -/
abbrev pow_mod_correct := _root_.powMod_correct

/-- Local multiplication power law used by the early arithmetic engine. -/
abbrev mul_pow := _root_.mul_pow_local

/-- Cubic expansion driving the cascade recurrence. -/
abbrev cubic_expansion := _root_.cubic_expansion

/-- Recurrence for the cascade constant. -/
abbrev cascade_recursion := _root_.c_recursion

/-- One-step low-tower cubic identity. -/
abbrev low_tower_cubic_step := _root_.lte_cubic_step

/-- Low-tower identity: `4^(3^s)` is `1` plus a controlled ternary tail. -/
abbrev low_tower_identity := _root_.lte_identity

/-- Mod-three bridge signature of the cascade constant. -/
abbrev cascade_mod_three := _root_.c_mod3

/-- Mod-nine bridge signature of the cascade constant. -/
abbrev cascade_mod_nine := _root_.c_mod9

/-- First stable cascade value. -/
abbrev stable_cascade_one := _root_.c_stable_1

/-- Second stable cascade value. -/
abbrev stable_cascade_two := _root_.c_stable_2

/-- Third stable cascade value. -/
abbrev stable_cascade_three := _root_.c_stable_3

/-- Fourth stable cascade value. -/
abbrev stable_cascade_four := _root_.c_stable_4

/-- Stable mod-three law for the cascade residue. -/
abbrev stable_cascade_mod_three := _root_.c_stable_mod3

/-- Stable mod-nine law for the cascade residue. -/
abbrev stable_cascade_mod_nine := _root_.c_stable_mod9

/-- Stable mod-eighty-one law for the cascade constant. -/
abbrev cascade_mod_eighty_one_stable := _root_.c_mod81_stable

/-- Stable mod-two-hundred-forty-three law for the cascade constant. -/
abbrev cascade_mod_two_four_three_stable := _root_.c_mod243_stable

/-- Cascade lift from a finite prefix witness into a full four-power witness. -/
abbrev cascade_lift := _root_.cascade_lift

end Genesis
end Worldtrace
