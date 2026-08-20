# GST Infinite-Control Production Design

## Purpose

Replace the old finite/termination-centered production seam with the strongest current GST V2 architecture. The current failure (`h_creation_for_4pow` being unavailable after the finish runner truncates the quarantined legacy chain) is not repaired by re-exposing the legacy theorem. Instead, the production proof is restructured so that old `h_creation_for_4pow`, old `gst_duality`, and residual Ω termination are no longer foundational dependencies.

## Core ontology

The production engine treats information as globally conserved across all observation depths. Local event labels such as CREATE, DESTROY, SURVIVE, and NEITHER describe changes of representation in one coordinate or space; they do not assert global creation or annihilation of information.

The new proof spine is all-Nat. Finite support is represented as a horizon inside an infinite controller, not as termination of the controller. In particular, a visible Future channel reaching zero means its information has been transferred into the conserved Past ledger.

## Three-space transport

The old `gst_duality` concept is demoted. The production transport layer is explicitly tri-space: NULL, ALT−, and GST+. Existing exact V2 transition/carry equations remain the arithmetic basis. Compatibility theorems may preserve old public names temporarily, but no new proof may depend on the old two-space ontology.

## Infinite-control invariants

The production core is allowed to use and combine only kernel-checked exact invariants, including:

1. Ω Past/Future additive conservation at every natural depth.
2. Π/U multiplicative origin conservation at every natural depth.
3. Exact cardinal/world equations parameterized by arbitrary world cardinality K.
4. Six-world projections and cofinal finite-origin synchronization/collision principles.
5. Finite natural support as a horizon theorem inside a Nat-indexed stream.
6. Exact retained-offset origin recursion preserving offset, multiplier, seed, and origin energy.
7. Existing physical/canonical causality and gate equations that do not depend on residual Ω termination.

## Production replacement seam

The old failing direct-induction seam

`h_creation_for_4pow -> gst_duality -> ...`

is removed from the proof strategy.

The old circular prefix-one seam

`prefix-one bad -> residual Ω termination -> False`

is also removed.

The new canonical target is an infinite-control collision theorem of the following logical shape:

```lean
theorem gst_v2_infinite_prefix_one_collision
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  ...
```

Its implementation may factor through a stronger residual infinite-support bridge:

```lean
theorem gst_canonical_residual_infinite_support_bridge
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hn3 : n % 3 ≠ 0)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) :
    InfiniteTernarySupportS n := by
  ...
```

The contradiction is then finite-origin versus all-depth support/control, not proof by a terminal event.

## Controlled-chaos meaning

"Controlled chaos" means local orbit behavior may branch among exact GST states, but every branch remains constrained by global invariants. The proof must preserve enough information to project the same orbit at arbitrary finite depth K. It must not discard the origin state merely to derive a local contradiction.

## Legacy policy

The following are legacy-only and may not be reintroduced as production foundations:

- quarantined `h_creation_for_4pow`;
- old two-space `gst_duality` as an ontology;
- `gst_omega_termination_s1`, `gst_omega_termination_s3`, `gst_omega_termination_stable`, or `gst_residual_omega_termination` as required production steps;
- any theorem whose only justification is a finite search bound for the large universal branch;
- any `sorry`, `admit`, hidden axiom, or `native_decide` escape for a universal proposition.

Legacy theorem names may remain as compatibility adapters only if they are derived from the new V2 core and are not used to hide a missing theorem.

## Module boundaries

New production components should be small and dependency-directed:

- `GSTInfiniteControlProduction.lean`: production-facing conserved all-Nat interfaces and aliases to already kernelized V2 invariants.
- `GSTInfinitePrefixOneCollision.lean`: the new prefix-one/residual collision theorem and its private supporting lemmas.
- `ErdosTernary2.lean`: consumer wiring only; replace the old circular contradiction body with the new collision theorem and redirect residual construction through the new prefix-one theorem.

Scratch modules remain evidence/prototyping sources. Production modules may import the strongest scratch files temporarily if they are kernel-clean; once comparator is green, they can be consolidated without changing theorem statements.

## Verification

Every promoted theorem must pass:

1. a dedicated Lean smoke that initially fails at the missing production theorem;
2. `lake env lean` on the smoke/production module;
3. `#print axioms` inspection showing no `sorryAx` or custom axioms;
4. `lake build`;
5. `bash scripts/sorry_check.sh`;
6. `bash scripts/comparator.sh` printing exactly `Your solution is okay!`.

No completion claim is allowed before the fresh comparator run passes.
