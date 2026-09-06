# Problem 406 public API expansion

This pass expands the reviewer-facing theorem surface under the confirmed umbrella name **Worldtrace Arithmetic**.

## Policy

The proof corpus contains many internal declarations whose names encode their construction history.  Renaming all of them in place would be risky and would create churn through the proof stack.

The professional presentation layer therefore uses wrappers:

- internal proof identifiers remain stable;
- the historical compatibility surface remains under `GST.*`;
- the new umbrella surface begins under `Worldtrace.*`;
- the theorem map compile-checks the exposed surface;
- the full theorem universe remains indexed in the FINISHER manifest.

## Current public modules

| Module | Purpose |
| --- | --- |
| `Worldtrace.PublicAPI` | umbrella public facade for the full mathematics |
| `GST.Problem406.Core` | final theorem and ternary digit predicates |
| `GST.Problem406.FourPower` | even-exponent/four-power wave layer |
| `GST.Problem406.PrefixOne` | creation-master and prefix-one bridge layer |
| `GST.Problem406.LocalCell` | finite local cell/right-chord classification |
| `GST.Problem406.Navigation` | navigation witness and finite endpoint bridge |

## Professional categories

| Category | Meaning |
| --- | --- |
| Worldtrace Arithmetic | full branch-level framework |
| True Duality Transcendence | early arithmetic/cascade genesis layer |
| Ternary Event Arithmetic | digit and prefix mechanics |
| Carry-Information Theory | exact carry transport and affine carry state |
| Residue Tower Theory | stable modular fingerprints |
| Four-Power Dynamics | adjacent power and exponent-prefix machinery |
| General Space Theory | navigation-geometric pillar |
| Canonical Collision Theory | collision, wave, bad-trace, and terminal closure |
| Phase-Cycle Algebra | NULL regeneration and shared information transport |
| Finite Certificate Theory | decidable local certificates and base cases |
| Problem 406 Layer | final theorem surface |

## Style baseline

The public layer follows the same broad style used in mature Lean theorem files: module-level documentation, a small main-declarations surface, local/private machinery kept internal, and docstrings on promoted declarations.

## Next expansion target

The next API pass should create layer-level modules:

```text
Worldtrace.Ternary
Worldtrace.Carry
Worldtrace.Residue
Worldtrace.FourPower
Worldtrace.Navigation
Worldtrace.Collision
Worldtrace.Phase
Worldtrace.Certificate
```

Each module should expose only stable mathematical names.  Internal historical names should be migrated later through a dependency-safe rename pass.
