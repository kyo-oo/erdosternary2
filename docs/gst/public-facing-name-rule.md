# Public naming rule: Worldtrace Arithmetic and GST

This repository now uses **Worldtrace Arithmetic** as the public umbrella name for the full mathematics.

The Lean namespace `GST` remains the historical abbreviation for **General Space Theory**, which is the navigation-geometric pillar inside Worldtrace Arithmetic.

## Rule

Public prose must use:

```text
Worldtrace Arithmetic
```

when referring to the whole framework.

Public prose must use:

```text
General Space Theory (GST)
```

only when referring to the GST/navigation/geometric pillar.

## Why Lean still uses `GST`

Lean names need to remain stable for proof compatibility.  The historical namespace remains:

```lean
GST
```

For example:

```lean
GST.Problem406.contains_two_digit_of_nine_le
GST.Arithmetic.digit3
GST.FourPower.CommonTwo
```

## New umbrella import

New public-facing imports should prefer:

```lean
import Worldtrace.PublicAPI
```

Primary reviewer-facing checks:

```lean
#check Worldtrace.erdos_ternary_two
#check Worldtrace.four_power_contains_digit_two
```

## Prose examples

Use:

```text
Worldtrace Arithmetic combines ternary event arithmetic, carry-information
transport, four-power dynamics, collision closure, and General Space Theory
navigation certificates.
```

Use:

```text
General Space Theory (GST) supplies the navigation-geometric pillar.
```

Avoid:

```text
GST is the whole mathematical framework.
```

## Public API interpretation

The API path:

```lean
GST.FourPower.exponentPrefix
```

should be described in prose as:

```text
Worldtrace Arithmetic's four-power exponent-prefix layer, using the historical
GST namespace.
```

This keeps Lean stable while making the mathematical identity accurate.
