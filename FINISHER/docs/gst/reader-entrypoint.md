# General Space Theory (GST) reader entrypoint

Start here when reading the project as mathematics rather than as raw Lean files.

## One-sentence view

General Space Theory (GST), developed by Nidhish, is the structural graph/navigation framework that organizes the ternary digit, carry, four-power, and certificate machinery used in the Problem 406 proof.

## Read in this order

1. `docs/gst/README.md`
2. `docs/gst/major-theorem-layers.md`
3. `docs/gst/theorem-taxonomy.md`
4. `docs/gst/theorem-index.md`
5. `docs/gst/module-map.md`
6. `docs/gst/glossary.md`
7. `docs/gst/graph-v2-overview.md`
8. `docs/gst/proof-dependency-map-v2.md`
9. `docs/gst/tactic-index.md`
10. `docs/gst/audit-hygiene.md`

## Main Lean imports

```lean
import GST.PublicAPI
import GST.Problem406
```

## Main public theorem

```lean
GST.Problem406.contains_two_digit_of_nine_le
```

## Public naming rule

In prose, write:

```text
General Space Theory (GST)
```

In Lean, use:

```lean
GST
```

This keeps the mathematical identity clear while keeping Lean names usable.
