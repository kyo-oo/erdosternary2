# General Space Theory inside Worldtrace Arithmetic

General Space Theory (GST) is the navigation-geometric pillar of **Worldtrace Arithmetic**.  It is not the full umbrella name for the mathematics in this repository.

This file separates GST from the surrounding theorem families so the project does not look like a flat pile of declarations or a single-theory monoculture.

## Umbrella framework

```text
Worldtrace Arithmetic
```

Worldtrace Arithmetic studies arithmetic objects as trace-bearing worlds whose digit, carry, residue, navigation, collision, and obstruction states remain coupled across transformations.

## GST pillar

GST supplies:

- spaces;
- graph states;
- Happy gates;
- navigation witnesses;
- creation certificates;
- finite and infinite transport interfaces.

Public-facing GST concepts include:

```lean
GST.Arithmetic.HappyCell
GST.Arithmetic.Navigation
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
```

## Surrounding Worldtrace layers

The proof also depends on several non-GST layers.

| Layer | Role |
| --- | --- |
| True Duality Transcendence | Early arithmetic bridge and cascade engine. |
| Ternary Event Arithmetic | Digit, prefix, and finite-position machinery. |
| Carry-Information Theory | Exact carry transport and affine carry state. |
| Residue Tower Theory | Stable low-residue fingerprints. |
| Four-Power Dynamics | Adjacent powers, common-two witnesses, exponent-prefix obstruction. |
| Canonical Collision Theory | Collision, bad-trace, wave, and terminal-extinction closure. |
| Phase-Cycle Algebra | NULL regeneration and shared information transport. |
| Finite Certificate Theory | Kernel-decidable local certificates and base closures. |

## GST Graph V2 / navigation layer

This layer explains how local arithmetic states become graph/navigation objects.

It connects:

```text
digit/carry cell
  -> HappyCell gate
  -> Navigation witness
  -> CreationCertificate
```

## Ternary arithmetic layer

This layer contains the digit and prefix mechanics.

Public-facing names include:

```lean
GST.Arithmetic.digit3
GST.Arithmetic.prefix_slice_digit_exact
GST.Arithmetic.canonical_tail_state_isomorphism
```

## Carry dynamics layer

This layer controls exact carry behavior under multiplication by four.

Public-facing names include:

```lean
GST.Arithmetic.carry4
GST.Arithmetic.carry4_lt_four
GST.Arithmetic.carry4_forward_exact
GST.Arithmetic.canonical_tail_happy_iff
```

## Four-power common-two layer

This layer handles common ternary digit-two witnesses for consecutive powers of four.

Public-facing names include:

```lean
GST.FourPower.CommonTwo
GST.FourPower.DirectExistence
GST.FourPower.common_two_has_source_two
GST.FourPower.common_two_has_target_two
GST.FourPower.common_two_of_mod9_five_or_six
```

## Exponent-prefix obstruction layer

This layer exposes the parametric exponent-prefix/trit law.

Public-facing names include:

```lean
GST.FourPower.exponentPrefix
GST.FourPower.exponentTrit
GST.FourPower.exponent_prefix_trit_decomposition
GST.FourPower.pow4_pair_from_exponent_trit
GST.FourPower.no_common_two_exponent_trit_obstruction
```

## Provider and certificate bridge layer

This layer turns arithmetic existence into navigation/certificate language.

Public-facing names include:

```lean
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
GST.FourPower.creation_certificate_to_navigation
GST.FourPower.four_power_navigation_of_master
```

## Problem 406 theorem layer

This is the final public theorem surface.

```lean
Worldtrace.erdos_ternary_two
GST.Problem406.contains_two_digit_of_nine_le
```

It wraps:

```lean
erdos_ternary_2_universal
```

## Management rule

Use `Worldtrace Arithmetic` as the public branch name.  Use `GST` for the navigation-geometric pillar and historical Lean namespace.  The public API should expose a stable subset of major theorem names while the full theorem universe remains indexed in generated manifests and curated index files.
