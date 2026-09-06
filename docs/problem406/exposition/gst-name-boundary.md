# General Space Theory (GST) name boundary

`GST` is the Lean abbreviation for **General Space Theory**.

The repository should keep these two levels separate:

| Level | Usage |
| --- | --- |
| Mathematical prose | General Space Theory (GST) |
| Lean namespace | `GST` |
| Public API import | `GST.PublicAPI` |
| Problem 406 endpoint | `GST.Problem406.contains_two_digit_of_nine_le` |

## Boundary

The name `GST` should never be presented as an unexplained acronym in public-facing documentation.

First mention:

```text
General Space Theory (GST)
```

Later mention:

```text
GST
```

## Reason

The mathematics is the theory framework. The namespace is only the packaging.
