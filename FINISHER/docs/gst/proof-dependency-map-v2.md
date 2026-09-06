# General Space Theory (GST) proof dependency map

This file describes the high-level dependency flow from General Space Theory objects to the final Problem 406 theorem.

It is a reader-facing map, not a replacement for the Lean dependency graph.

## Top-level flow

```text
General Space Theory core language
  -> GST Graph V2/navigation layer
  -> ternary digit arithmetic
  -> carry dynamics under multiplication by four
  -> common-two witnesses for consecutive four-powers
  -> exponent-prefix obstruction law
  -> creation certificate bridge
  -> final Problem 406 theorem
```

## Formal public endpoint

The public endpoint is:

```lean
GST.Problem406.contains_two_digit_of_nine_le
```

It wraps the checked monolith theorem:

```lean
erdos_ternary_2_universal
```

## Dependency groups

| Group | Role | Representative public names |
| --- | --- | --- |
| GST core | Space/navigation language | `GST.Arithmetic.HappyCell`, `GST.Arithmetic.Navigation` |
| Ternary arithmetic | Digit projection and tail transport | `GST.Arithmetic.digit3`, `GST.Arithmetic.prefix_slice_digit_exact` |
| Carry dynamics | Exact base-three carry recurrence | `GST.Arithmetic.carry4`, `GST.Arithmetic.carry4_forward_exact` |
| Four-power witnesses | Shared digit-two rows for `4^K`, `4^(K+1)` | `GST.FourPower.CommonTwo` |
| Prefix law | Exponent-prefix and trit decomposition | `GST.FourPower.exponentPrefix`, `GST.FourPower.exponentTrit` |
| Certificate bridge | Converts arithmetic witnesses to navigation | `GST.FourPower.CreationCertificate` |
| Problem 406 | Final theorem surface | `GST.Problem406.contains_two_digit_of_nine_le` |

## Why this map exists

The project has a large theorem base. A raw list of declarations is useful for audit, but not enough for mathematical reading.

This map tells reviewers where each theorem group sits in the proof architecture:

```text
local arithmetic facts are not isolated tricks;
they feed the graph/navigation layer;
the graph/navigation layer feeds certificate construction;
the certificate construction feeds the final Problem 406 theorem.
```

## Audit relation

The public surface is smoke-checked by:

```lean
GST.Audit.PublicSurfaceCheck
```

Axiom-report hygiene is tracked by:

```lean
GST.Audit.Problem406AxiomReport
```

Generated declaration coverage is tracked under:

```text
docs/gst/generated/
```

## Frozen-source rule

This map documents the dependency structure over the existing checked artifacts. It does not authorize rewriting the proof monolith. The current green branch keeps `ErdosTernary2.lean` untouched.
