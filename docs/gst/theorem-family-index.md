# GST Theorem Family Index

This file organizes the 630+ theorem/declaration surface by mathematical role. It is not a complete generated manifest. The full manifest should be generated from Lean source in a later tooling pass and then linked back to these families.

The goal is to give reviewers a map before they enter the monolith.

## Indexing policy

Every important theorem should eventually have:

| Field | Meaning |
|---|---|
| Family | Mathematical subsystem. |
| Source module | Lean file where the theorem lives. |
| Internal name | Current declaration name. |
| Public alias | Clean review-facing name if the theorem is part of the public API. |
| Role | Definition, local lemma, bridge theorem, obstruction, certificate, or final theorem. |
| Reviewer priority | `core`, `support`, `internal`, or `historical`. |

Only the public API and core bridge theorem names need beautiful aliases. Most support lemmas should stay internal and be indexed, not renamed.

## Family A — Problem 406 certificate

| Representative declaration | Source | Role | Public alias policy |
|---|---|---|---|
| `erdos_ternary_2` | `questions/deepmind_problem_406/Solution.lean` | Comparator-facing theorem. | Keep exact benchmark name. |
| `GST.Problem406.contains_two_digit_of_nine_le` | `GST/Problem406/PublicAPI.lean` | Clean public theorem wrapper. | Public name. |
| `erdos_ternary_2_universal` | `ErdosTernary2.lean` | Internal monolith theorem imported by public wrapper. | Do not rename directly. |
| `noTernaryTwo` | `ErdosTernary2.lean` | Internal predicate for no ternary digit two. | May receive a documented public alias later. |

## Family B — Canonical ternary state

| Representative declaration | Source | Role |
|---|---|---|
| `digit3` | `GSTCanonicalTailStateIso.lean`, `GSTFourPowerDirectResidue.lean` | Ternary digit extraction. |
| `carry4` | `GSTCanonicalTailStateIso.lean` | x4/base-3 carry from lower prefix. |
| `HappyCell` | `GSTCanonicalTailStateIso.lean` | Physical gate: digit two with carry zero or three. |
| `Navigation` | `GSTCanonicalTailStateIso.lean` | Existence of a HappyCell witness. |
| `carry4_lt_four` | `GSTCanonicalCarryDynamics.lean` | Carry bound. |
| `carry4_forward_exact` | `GSTCanonicalCarryDynamics.lean` | Exact carry regeneration. |
| `canonical_tail_state_isomorphism` | `GSTCanonicalTailStateIso.lean` | Tail-state isomorphism under seed-zero prefix. |

## Family C — GST tactics and finite-state helpers

| Representative declaration | Source | Role |
|---|---|---|
| `nat_lt_four_cases` | `GSTTactic.lean` | Finite carry case split. |
| `nat_lt_three_cases` | `GSTTactic.lean` | Finite digit case split. |
| `gst_omega` | `GSTTactic.lean` | Local GST arithmetic/decreasing-goal tactic. |
| `gst_end` | `GSTTactic.lean` | Final closing tactic for selected residual branches. |
| `gst_carry_cases` | `GSTTactic.lean` | Macro for carry case split. |
| `gst_digit_cases` | `GSTTactic.lean` | Macro for ternary digit case split. |

## Family D — 2D Mixed Emergence

| Representative declaration | Source | Role |
|---|---|---|
| `microOutput` | `GST2DMixedEmergence.lean` | One literal x2/base-3 microscopic output. |
| `outDigit` | `GST2DMixedEmergence.lean` | Exact x4/base-3 output digit. |
| `nextCarry` | `GST2DMixedEmergence.lean` | Exact x4/base-3 next carry. |
| `sevenKernel` | `GST2DMixedEmergence.lean` | Two microscopic x2 layers composing one x4 GST cell. |
| `surviveI` | `GST2DMixedEmergence.lean` | Microscopic BIG2-to-BIG2 survive incidence. |
| `mixed_cell_emergence` | `GST2DMixedEmergence.lean` | Local mixed 2D GST emergence equation. |
| `mixed_rectangle_emergence` | `GST2DMixedEmergence.lean` | Full finite rectangle divergence theorem. |
| `happy_chord_dichotomy` | `GST2DMixedEmergence.lean` | Splits Happy realization into NULL and GST+ chords. |

## Family E — GST Graph V2

| Representative declaration | Source | Role |
|---|---|---|
| `Cell` | `GSTGraphV2Production.lean` | Production graph cell object. |
| `Sheet` | `GSTGraphV2Production.lean` | Infinite grid of cells. |
| `Lattice` | `GSTGraphV2Production.lean` | Cell grid plus horizontal and vertical edges. |
| `Rectangle` | `GSTGraphV2Production.lean` | Finite observed rectangle on the same infinite lattice. |
| `OriginFrame` | `GSTGraphV2Production.lean` | Full/neutral/phased origin coordinates. |
| `ResidualFrame` | `GSTGraphV2Production.lean` | Residual production frame. |
| `CanonicalCutFrame` | `GSTGraphV2Production.lean` | Canonical production-cut frame. |
| `horizontal_digit_exact` | `GSTGraphV2ProductionLaws.lean` | Horizontal x4 digit edge law. |
| `vertical_carry_exact` | `GSTGraphV2ProductionLaws.lean` | Vertical ternary carry edge law. |
| `navigation_nullspace_flux_exact` | `GSTGraphV2ProductionLaws.lean` | Equation-I/nullspace flux identity. |

## Family F — U2D and crossing-charge domination

| Representative declaration | Source | Role |
|---|---|---|
| `sharpTerminalPotential` | `GSTU2DSharpCrossingBlock.lean` | Terminal digit potential for sharp crossing. |
| `sharpTerminalPotential_step` | `GSTU2DSharpCrossingBlock.lean` | One-step preservation of sharp potential. |
| `reverseCrossCode_ge_sharp_of_leading_happy` | `GSTU2DSharpCrossingBlock.lean` | Sharp all-width bound from a leading Happy cell. |
| `reverseCrossCode_ge_global_floor` | `GSTU2DSharpCrossingBlock.lean` | Global floor for a physical horizontal row. |
| `weightedCrossPrefix_positive_of_top_leading_happy` | `GSTU2DSharpCrossingBlock.lean` | Highest-Happy-row domination theorem. |

## Family G — Four-power direct arithmetic

| Representative declaration | Source | Role |
|---|---|---|
| `lteCoeff` | `GSTFourPowerDirectResidue.lean` | LTE quotient for `4^(3^r)`. |
| `pow4_three_power_lte_exact` | `GSTFourPowerDirectResidue.lean` | Exact LTE identity. |
| `lteCoeff_mod3_one` | `GSTFourPowerDirectResidue.lean` | LTE quotient congruence. |
| `pow4_scaled_mod_next` | `GSTFourPowerDirectResidue.lean` | Scaled exponent periodicity modulo next ternary cut. |
| `digit3_eq_of_mod_next` | `GSTFourPowerDirectResidue.lean` | Digit determined by residue modulo `3^(p+1)`. |
| `pow4_digit_period` | `GSTFourPowerDirectResidue.lean` | Row `p` periodicity in exponent. |
| `pow4_exponent_trit_lift_digit` | `GSTFourPowerDirectResidue.lean` | Exponent-trit row lift. |

## Family H — Row classifiers and direct obstructions

| Representative declaration | Source | Role |
|---|---|---|
| `row_two_overlap_iff_mod9_five_or_six` | `GSTFourPowerDirectResidue.lean` | Exact row-two classifier. |
| `row_three_overlap_of_mod27_classes` | `GSTFourPowerDirectResidue27.lean` | Row-three modulo 27 classifier. |
| `RowFourClass` | `GSTFourPowerDirectResidue81.lean` | Fourteen row-four residue classes modulo 81. |
| `row_four_overlap_of_mod81_classes` | `GSTFourPowerDirectResidue81.lean` | Row-four classifier. |
| `no_common_two_forbids_mod9_five_six` | `GSTFourPowerDirectResidue.lean` | Counterexample exclusion. |
| `no_common_two_forbids_mod27_classes` | `GSTFourPowerDirectResidue27.lean` | Counterexample exclusion. |
| `no_common_two_forbids_mod81_classes` | `GSTFourPowerDirectResidue81.lean` | Counterexample exclusion. |
| `no_common_pow4_forbids_all_22` | `GSTFourPowerDirectNo22.lean` | No adjacent `22` source blocks under no-common trace. |

## Family I — Exponent-prefix / exponent-trit law

| Representative declaration | Source | Role |
|---|---|---|
| `exponentPrefix` | `GSTFourPowerExponentTritObstruction.lean` | Low ternary prefix of exponent. |
| `exponentTrit` | `GSTFourPowerExponentTritObstruction.lean` | Current ternary trit of exponent. |
| `exponent_prefix_trit_decomposition` | `GSTFourPowerExponentTritObstruction.lean` | Exact base-three exponent decomposition. |
| `pow4_pair_from_exponent_trit` | `GSTFourPowerExponentTritObstruction.lean` | Actual exponent-trit pair formula. |
| `row_common_two_iff_prefix_killing_trit` | `GSTFourPowerExponentTritObstruction.lean` | Exact common-two normal form. |
| `no_common_two_exponent_trit_obstruction` | `GSTFourPowerExponentTritObstruction.lean` | Parametric obstruction on every exponent trit. |

## Family J — Affine channel automaton and Chat-2

| Representative declaration | Source | Role |
|---|---|---|
| `lowDigit` | `GSTFourPowerAffineChannelAutomaton.lean` | Least ternary digit of channel source. |
| `tail3` | `GSTFourPowerAffineChannelAutomaton.lean` | One-trit tail. |
| `channelOut` | `GSTFourPowerAffineChannelAutomaton.lean` | Low output digit of `x ↦ 4x+c`. |
| `channelNext` | `GSTFourPowerAffineChannelAutomaton.lean` | Next carry/channel state. |
| `BadChannel` | `GSTFourPowerAffineChannelAutomaton.lean` | Global badness of one affine channel. |
| `pairCommonTwo_channel_iff` | `GSTFourPowerAffineChannelAutomaton.lean` | Master affine-channel recursion. |
| `badChannel_iff` | `GSTFourPowerAffineChannelAutomaton.lean` | Complement form of channel recursion. |
| `chat2_commonTwo_iff_affine_channel_one` | `GSTFourPowerDirectChat2Application.lean` | Direct problem equals affine channel one. |
| `chat2_noCommonTwo_iff_bad_channel_one` | `GSTFourPowerDirectChat2Application.lean` | Counterexample equals bad state `B₁`. |
| `chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one` | `GSTFourPowerDirectChat2Application.lean` | Final bad-channel equivalence. |

## Family K — Provider and certificate pipeline

| Representative declaration | Source | Role |
|---|---|---|
| `CommonTwo` | `GSTFourPowerDirectExistence.lean` | Common digit-two witness for consecutive powers of four. |
| `FourPowerDirectExistence` | `GSTFourPowerDirectExistence.lean` | Direct universal arithmetic target. |
| `CommonTwoGeThree` | `GSTFourPowerHappyProvider.lean` | Row-three-or-higher common-two witness. |
| `PrefixHitGeThree` | `GSTFourPowerHappyProvider.lean` | Parametric prefix-hit provider target. |
| `FourPowerHappyGeThreeProvider` | `GSTFourPowerDirectExistenceProviderPipeline.lean` | Physical Happy-row provider gate. |
| `FourPowerCommonTwoGeThreeProvider` | `GSTFourPowerDirectExistenceProviderPipeline.lean` | Sharpened direct witness provider gate. |
| `FourPowerDirectNoBadAffineChannelOne` | `GSTFourPowerDirectExistenceProviderPipeline.lean` | Bad affine channel kill target. |
| `CreationCertificate` | `GSTFourPowerOntologicalAdapter.lean` | Historical CREATE certificate. |
| `creation_certificate_to_navigation` | `GSTFourPowerOntologicalAdapter.lean` | Certificate-to-Navigation bridge. |

## Family L — Prefix-one ontological escape

| Representative declaration | Source | Role |
|---|---|---|
| `prefix_one_exponent_ge_twelve` | `GSTPrefixOneOntologicalEscape.lean` | Prefix-one exponents enter the four-power range. |
| `gst_prefix_one_ontological_escape_of_master` | `GSTPrefixOneOntologicalEscape.lean` | Prefix-one escape from creation master. |
| `gst_four_power_creation_certificate_noAxiom_from_provider` | `GSTPrefixOneOntologicalEscape.lean` | No-axiom transplant entrypoint from Happy provider. |
| `gst_four_power_creation_certificate_noAxiom_from_commonTwoGeThree` | `GSTPrefixOneOntologicalEscape.lean` | No-axiom transplant entrypoint from row-three provider. |
| `gst_four_power_creation_certificate_noAxiom_from_prefixHitGeThree` | `GSTPrefixOneOntologicalEscape.lean` | No-axiom transplant entrypoint from prefix-hit law. |
| `gst_four_power_creation_certificate_noAxiom_from_no_bad_affine_channel_one` | `GSTPrefixOneOntologicalEscape.lean` | No-axiom transplant entrypoint from bad-channel kill. |

## Family M — Historical/internal monolith layer

The monolith contains many helper names created during the proof sprint, including names that are not public-quality. These should be preserved until a separate refactor proves that aliases, wrappers, and CI protect every theorem dependency.

Examples of names that should be treated as internal/historical rather than public surface:

- `GSTStep6Close`-style module names.
- Chronological labels and transplant comments.
- Tactical closure names tied to an old proof route.
- Debug/probe names used for CI exploration.

The public presentation should expose clean wrapper names instead of renaming these in place.
