# General Space Theory (GST) in the Problem 406 proof

General Space Theory (GST) is the structural theory framework developed by Nidhish and used in this repository to organize the arithmetic, graph, navigation, and certificate layers behind the Problem 406 formalization.

## Position in the proof stack

Problem 406 is the final benchmark-facing theorem. General Space Theory is the organizing framework behind the proof architecture.

The proof stack should be read as:

```text
General Space Theory framework
  -> GST Graph V2/navigation layer
  -> ternary digit and carry arithmetic
  -> four-power common-two engine
  -> exponent-prefix obstruction law
  -> creation certificate bridge
  -> Problem 406 final theorem
```

## Why this matters

The public API uses short Lean names such as:

```lean
GST.Arithmetic.digit3
GST.FourPower.CommonTwo
GST.Problem406.contains_two_digit_of_nine_le
```

Those names are intentionally compact for Lean. In exposition, they should be introduced as parts of **General Space Theory (GST)** so readers understand the mathematical framework rather than seeing only an unexplained acronym.

## Main public endpoint

```lean
GST.Problem406.contains_two_digit_of_nine_le
```

This is the public wrapper around:

```lean
erdos_ternary_2_universal
```

## Related GST documentation

See:

```text
docs/gst/README.md
docs/gst/theorem-index.md
docs/gst/theorem-taxonomy.md
docs/gst/module-map.md
docs/gst/graph-v2-overview.md
docs/gst/glossary.md
docs/gst/public-facing-name-rule.md
```
