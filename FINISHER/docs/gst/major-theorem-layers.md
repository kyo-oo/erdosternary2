# General Space Theory (GST) major theorem layers

General Space Theory (GST) is the central framework of this repository, but the proof stack also contains other major theorem families that support it.

This file separates the main mathematical layers so the project does not look like a flat pile of Lean declarations.

## 1. General Space Theory framework

This is the conceptual core: spaces, graph states, navigation, gates, and certificates.

Public-facing concepts include:

```lean
GST.Arithmetic.HappyCell
GST.Arithmetic.Navigation
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
```

## 2. GST Graph V2 / navigation layer

This layer explains how local arithmetic states become graph/navigation objects.

It connects:

```text
digit/carry cell
  -> HappyCell gate
  -> Navigation witness
  -> CreationCertificate
```

## 3. Ternary arithmetic layer

This layer contains the digit and prefix mechanics.

Public-facing names include:

```lean
GST.Arithmetic.digit3
GST.Arithmetic.prefix_slice_digit_exact
GST.Arithmetic.canonical_tail_state_isomorphism
```

## 4. Carry dynamics layer

This layer controls exact carry behavior under multiplication by four.

Public-facing names include:

```lean
GST.Arithmetic.carry4
GST.Arithmetic.carry4_lt_four
GST.Arithmetic.carry4_forward_exact
GST.Arithmetic.canonical_tail_happy_iff
```

## 5. Four-power common-two layer

This layer handles common ternary digit-two witnesses for consecutive powers of four.

Public-facing names include:

```lean
GST.FourPower.CommonTwo
GST.FourPower.DirectExistence
GST.FourPower.common_two_has_source_two
GST.FourPower.common_two_has_target_two
GST.FourPower.common_two_of_mod9_five_or_six
```

## 6. Exponent-prefix obstruction layer

This layer exposes the parametric exponent-prefix/trit law.

Public-facing names include:

```lean
GST.FourPower.exponentPrefix
GST.FourPower.exponentTrit
GST.FourPower.exponent_prefix_trit_decomposition
GST.FourPower.pow4_pair_from_exponent_trit
GST.FourPower.no_common_two_exponent_trit_obstruction
```

## 7. Provider and certificate bridge layer

This layer turns arithmetic existence into GST navigation/certificate language.

Public-facing names include:

```lean
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
GST.FourPower.creation_certificate_to_navigation
GST.FourPower.four_power_navigation_of_master
```

## 8. Problem 406 theorem layer

This is the final public theorem surface.

```lean
GST.Problem406.contains_two_digit_of_nine_le
```

It wraps:

```lean
erdos_ternary_2_universal
```

## Management rule

The public API should expose a stable subset of major theorem names. The full theorem universe belongs in generated declaration manifests and curated index files.
