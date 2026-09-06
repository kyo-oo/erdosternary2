# Worldtrace theorem promotion map

This document maps the checked proof corpus into the public Worldtrace Arithmetic surface.

The rule is deliberate: the internal Lean proof names stay stable until a dependency-safe migration is completed.  Public promotion happens through wrapper modules with reviewer-facing names.

## Layer map

| Worldtrace layer | Public module | Proof-corpus source |
| --- | --- | --- |
| Genesis arithmetic | `Worldtrace.Genesis` | Early monolith constants, structural computation, low-tower identities, cascade lift |
| Ternary events | `Worldtrace.Ternary` | `noTernaryTwo`, `hasTernaryTwo`, prefix scanners, digit-position witnesses |
| Carry information | `Worldtrace.Carry` | `carryAtPos`, `gstCarry`, `gstAffineMulCarry`, seeded carry transport |
| Residue towers | `Worldtrace.Residue` | stable cascade residues and exponent-prefix/trit laws |
| Four-power dynamics | `Worldtrace.FourPower` | common-two witnesses, adjacent waves, four-power creation certificates |
| Navigation geometry | `Worldtrace.Navigation` | General Space Theory navigation constants, origin fingerprints, graph lifts |
| Collision closure | `Worldtrace.Collision` | local chord classification, residual NULL closure, physical rectangle conservation |
| Phase cycles | `Worldtrace.Phase` | NULL regeneration, 0->1->2->0 seed cycle, shared-information equations |
| Finite certificates | `Worldtrace.Certificate` | creation master, prefix-one lift, terminal finite gates |
| Umbrella theorem | `Worldtrace.PublicAPI` | final Problem 406 theorem and main aliases |

## Original 0--6k arithmetic genesis layer

These early declarations are now promoted because they are not disposable setup.  They are the arithmetic engine that creates the worldtrace:

| Internal declaration | Public name |
| --- | --- |
| `c` | `Worldtrace.Genesis.CascadeConstant` |
| `c_stable` | `Worldtrace.Genesis.StableCascadeConstant` |
| `powMod` | `Worldtrace.Genesis.powMod` |
| `powMod_correct` | `Worldtrace.Genesis.pow_mod_correct` |
| `cubic_expansion` | `Worldtrace.Genesis.cubic_expansion` |
| `c_recursion` | `Worldtrace.Genesis.cascade_recursion` |
| `lte_cubic_step` | `Worldtrace.Genesis.low_tower_cubic_step` |
| `lte_identity` | `Worldtrace.Genesis.low_tower_identity` |
| `c_mod3` | `Worldtrace.Genesis.cascade_mod_three` |
| `c_mod9` | `Worldtrace.Genesis.cascade_mod_nine` |
| `c_stable_mod3` | `Worldtrace.Genesis.stable_cascade_mod_three` |
| `c_stable_mod9` | `Worldtrace.Genesis.stable_cascade_mod_nine` |
| `c_mod81_stable` | `Worldtrace.Genesis.cascade_mod_eighty_one_stable` |
| `c_mod243_stable` | `Worldtrace.Genesis.cascade_mod_two_four_three_stable` |
| `cascade_lift` | `Worldtrace.Genesis.cascade_lift` |

## Ternary event layer

| Internal declaration | Public name |
| --- | --- |
| `noTernaryTwo` | `Worldtrace.Ternary.containsNoDigitTwo` |
| `hasTernaryTwo` | `Worldtrace.Ternary.containsDigitTwo` |
| `noTernaryTwoStruct` | `Worldtrace.Ternary.containsNoDigitTwoStruct` |
| `hasTernaryTwoStruct` | `Worldtrace.Ternary.containsDigitTwoStruct` |
| `hasD2AtPos` | `Worldtrace.Ternary.hasDigitTwoAtPosition` |
| `hasTwoInFirstK` | `Worldtrace.Ternary.hasDigitTwoInPrefix` |
| `hasTwoInFirstKStruct` | `Worldtrace.Ternary.hasDigitTwoInPrefixStruct` |
| `noTernaryTwo_eq_struct` | `Worldtrace.Ternary.no_digit_two_eq_struct` |
| `hasTwoInFirstK_eq_struct` | `Worldtrace.Ternary.prefix_scan_eq_struct` |
| `hasTwoInFirstK_pos` | `Worldtrace.Ternary.prefix_scan_has_position` |

## Carry-information layer

| Internal declaration | Public name |
| --- | --- |
| `carryAtPos` | `Worldtrace.Carry.structuralCarry` |
| `gstCarry` | `Worldtrace.Carry.carry` |
| `gstDigit` | `Worldtrace.Carry.digit` |
| `gstAffineMulCarry` | `Worldtrace.Carry.affineCarry` |
| `carryAtPos_bound` | `Worldtrace.Carry.structural_carry_bound` |
| `gst_decide_survival` | `Worldtrace.Carry.digit_two_survives_times_four` |
| `gstCarry_forward_exact_all` | `Worldtrace.Carry.carry_forward_exact` |
| `gst_seeded_affine_carry_semigroup` | `Worldtrace.Carry.seeded_affine_carry_semigroup` |
| `gst_shared_information_carry_equation` | `Worldtrace.Carry.shared_information_carry_equation` |

## Navigation and collision unlock layer

| Internal declaration | Public name |
| --- | --- |
| `gstNavigationConstant` | `Worldtrace.Navigation.Constant` |
| `GSTNavigationWitness` | `Worldtrace.Navigation.Witness` |
| `gst_navigation_decomposition` | `Worldtrace.Navigation.decomposition` |
| `gst_orthogonal_origin_split` | `Worldtrace.Navigation.orthogonal_origin_split` |
| `gst_orthogonal_origin_fingerprint` | `Worldtrace.Navigation.orthogonal_origin_fingerprint` |
| `gst_navigation_constant_general_recurrence` | `Worldtrace.Navigation.constant_general_recurrence` |
| `gst_navigation_position_universal` | `Worldtrace.Navigation.position_universal` |
| `gstResidualNullTerminalS` | `Worldtrace.Collision.ResidualNullTerminal` |
| `gst_residual_null_terminal_happy_allS` | `Worldtrace.Collision.residual_null_terminal_happy_all` |
| `gst_exact_power_rectangle_conservationS` | `Worldtrace.Collision.exact_power_rectangle_conservation` |

## Phase and certificate layer

| Internal declaration | Public name |
| --- | --- |
| `gst_null_two_regenerates` | `Worldtrace.Phase.null_two_regenerates` |
| `gst_plus_two_propagates` | `Worldtrace.Phase.plus_two_propagates` |
| `gst_seeded_shared_information_equationS` | `Worldtrace.Phase.seeded_shared_information_equation` |
| `gst_phase01_shared_informationS` | `Worldtrace.Phase.phase_zero_to_one_shared_information` |
| `gst_phase12_shared_informationS` | `Worldtrace.Phase.phase_one_to_two_shared_information` |
| `gst_phase20_shared_informationS` | `Worldtrace.Phase.phase_two_to_zero_shared_information` |
| `gst_four_power_creation_master_inline` | `Worldtrace.Certificate.four_power_creation_master` |
| `gst_prefix_one_navigation_lift` | `Worldtrace.Certificate.prefix_one_navigation_lift` |

## Final theorem surface

| Internal declaration | Public name |
| --- | --- |
| `erdos_ternary_2_universal` | `Worldtrace.erdos_ternary_two` |
| `erdos_ternary_2_even_universal` | `Worldtrace.four_power_contains_digit_two` |

## Migration policy

A later internal-name migration may neutralize historical names.  It should only happen after:

1. the Worldtrace wrappers compile;
2. a dependency manifest is generated;
3. references are rewritten file by file;
4. compatibility aliases are retained temporarily;
5. full CI is green.
