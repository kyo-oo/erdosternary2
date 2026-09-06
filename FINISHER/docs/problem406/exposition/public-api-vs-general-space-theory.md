# Public API versus General Space Theory (GST)

The public API uses short Lean namespaces. The mathematics behind those namespaces is **General Space Theory (GST)**.

This distinction matters.

## Lean namespace

Lean uses compact names:

```lean
GST.Arithmetic.digit3
GST.FourPower.CommonTwo
GST.Problem406.contains_two_digit_of_nine_le
```

These are practical proof-engine names.

## Mathematical framework

In exposition, these should be introduced as part of:

```text
General Space Theory (GST)
```

The reader should not be expected to guess what `GST` means.

## Correct public explanation

Use language like:

```text
General Space Theory (GST) supplies the graph/navigation framework.
The Lean public API exposes this framework under the namespace `GST`.
```

## Incorrect public explanation

Avoid language like:

```text
GST is the API namespace.
```

That is technically true but mathematically too weak. GST is the theory framework; the namespace is only the Lean packaging.

## Current project boundary

The current professionalization branch adds reader-facing structure around the checked theorem stack. It keeps the proof monolith untouched.
