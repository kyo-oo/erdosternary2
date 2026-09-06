# Problem 406 public API expansion

This pass expands the reviewer-facing theorem surface without renaming the
internal monolith declarations.

## Policy

The proof corpus contains many internal declarations whose names encode their
construction history.  Renaming all of them in place would be risky and would
create churn through the proof stack.  The professional presentation layer
therefore uses wrappers:

- internal proof identifiers remain stable;
- public names live under `GST.Problem406`;
- the theorem map compile-checks the exposed surface;
- the full theorem universe remains indexed in the FINISHER manifest.

## New public modules

| Module | Purpose |
| --- | --- |
| `GST.Problem406.Core` | final theorem and ternary digit predicates |
| `GST.Problem406.FourPower` | even-exponent/four-power wave layer |
| `GST.Problem406.PrefixOne` | creation-master and prefix-one bridge layer |
| `GST.Problem406.LocalCell` | finite local cell/right-chord classification |
| `GST.Problem406.Navigation` | navigation witness and finite endpoint bridge |

## Style baseline

The public layer follows the same broad style used in mathlib theorem files:
module-level documentation, a small main-declarations surface, local/private
machinery kept internal, and docstrings on promoted declarations.
