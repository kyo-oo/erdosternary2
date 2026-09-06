import Worldtrace.Genesis
import Worldtrace.Ternary
import Worldtrace.Carry
import Worldtrace.Residue
import Worldtrace.FourPower
import Worldtrace.Navigation
import Worldtrace.Collision
import Worldtrace.Phase
import Worldtrace.Certificate

/-!
# Worldtrace theorem map

Compile-checked index of the promoted Worldtrace Arithmetic surface.  This file
keeps the public layer honest: every listed name must resolve through Lean.
-/

-- Genesis / original 0--6k arithmetic engine
#check Worldtrace.Genesis.CascadeConstant
#check Worldtrace.Genesis.StableCascadeConstant
#check Worldtrace.Genesis.pow_mod_correct
#check Worldtrace.Genesis.cubic_expansion
#check Worldtrace.Genesis.cascade_recursion
#check Worldtrace.Genesis.low_tower_identity
#check Worldtrace.Genesis.cascade_mod_three
#check Worldtrace.Genesis.cascade_mod_nine
#check Worldtrace.Genesis.stable_cascade_mod_nine
#check Worldtrace.Genesis.cascade_lift

-- Ternary event arithmetic
#check Worldtrace.Ternary.containsNoDigitTwo
#check Worldtrace.Ternary.containsDigitTwo
#check Worldtrace.Ternary.hasDigitTwoAtPosition
#check Worldtrace.Ternary.hasDigitTwoInPrefix
#check Worldtrace.Ternary.no_digit_two_eq_struct
#check Worldtrace.Ternary.prefix_scan_eq_struct
#check Worldtrace.Ternary.prefix_scan_has_position
#check Worldtrace.Ternary.prefix_scan_contains_digit_two
#check Worldtrace.Ternary.residue_contains_digit_two

-- Carry-information theory
#check Worldtrace.Carry.structuralCarry
#check Worldtrace.Carry.carry
#check Worldtrace.Carry.digit
#check Worldtrace.Carry.affineCarry
#check Worldtrace.Carry.structural_carry_bound
#check Worldtrace.Carry.digit_two_survives_times_four
#check Worldtrace.Carry.carry_forward_exact
#check Worldtrace.Carry.seeded_affine_carry_semigroup
#check Worldtrace.Carry.shared_information_carry_equation

-- Residue towers and exponent-prefix laws
#check Worldtrace.Residue.exponentPrefix
#check Worldtrace.Residue.exponentTrit
#check Worldtrace.Residue.cascade_mod_two_four_three_stable
#check Worldtrace.Residue.exponent_prefix_trit_decomposition
#check Worldtrace.Residue.pow4_pair_from_exponent_trit
#check Worldtrace.Residue.no_common_two_exponent_trit_obstruction

-- Four-power dynamics
#check Worldtrace.FourPower.hasDigitTwo
#check Worldtrace.FourPower.CommonTwo
#check Worldtrace.FourPower.contains_digit_two
#check Worldtrace.FourPower.adjacent_identity
#check Worldtrace.FourPower.large_adjacent_wave
#check Worldtrace.FourPower.common_two_of_mod9_five_or_six
#check Worldtrace.FourPower.creation_master

-- Navigation geometry / GST pillar
#check Worldtrace.Navigation.Constant
#check Worldtrace.Navigation.Witness
#check Worldtrace.Navigation.decomposition
#check Worldtrace.Navigation.orthogonal_origin_split
#check Worldtrace.Navigation.orthogonal_origin_fingerprint
#check Worldtrace.Navigation.constant_general_recurrence
#check Worldtrace.Navigation.position_universal
#check Worldtrace.Navigation.graph_lift

-- Collision closure and terminal obstruction
#check Worldtrace.Collision.PhysicalTwoDigitClear
#check Worldtrace.Collision.happy_digit_two_right_chord_dichotomy
#check Worldtrace.Collision.ResidualNullTerminal
#check Worldtrace.Collision.residual_null_terminal_happy_all
#check Worldtrace.Collision.residual_null_origin_one_bad_impossible_all
#check Worldtrace.Collision.exact_power_rectangle_conservation

-- Phase cycles and finite certificates
#check Worldtrace.Phase.null_two_regenerates
#check Worldtrace.Phase.plus_two_propagates
#check Worldtrace.Phase.seeded_shared_information_equation
#check Worldtrace.Phase.phase_zero_to_one_shared_information
#check Worldtrace.Phase.phase_one_to_two_shared_information
#check Worldtrace.Phase.phase_two_to_zero_shared_information
#check Worldtrace.Certificate.creation_certificate_to_navigation
#check Worldtrace.Certificate.prefix_one_navigation_lift
#check Worldtrace.Certificate.residual_null_terminal_happy_all
