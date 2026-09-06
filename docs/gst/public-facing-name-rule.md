# General Space Theory (GST) public naming rule

This repository uses `GST` as the Lean namespace abbreviation for **General Space Theory**.

## Rule

Public prose must expand the name at first mention:

```text
General Space Theory (GST)
```

After first mention, `GST` is acceptable.

## Why Lean still uses `GST`

Lean names need to be short enough for proofs and imports. The namespace remains:

```lean
GST
```

For example:

```lean
GST.Problem406.contains_two_digit_of_nine_le
GST.Arithmetic.digit3
GST.FourPower.CommonTwo
```

## Why docs must expand it

Reviewers should understand that GST is a theory framework, not a generic internal label.

Use prose like:

```text
General Space Theory (GST) supplies the graph/navigation layer.
```

Avoid first mentions like:

```text
GST supplies the graph/navigation layer.
```

## Public API interpretation

The API path:

```lean
GST.FourPower.exponentPrefix
```

should be described in prose as:

```text
General Space Theory's four-power exponent-prefix API.
```

This keeps Lean clean while making the mathematical identity clear.
