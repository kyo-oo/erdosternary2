# GST V2 Infinite-Control Production Design

## Goal

Replace the legacy finite/termination/duality/creation proof corridor with a production GST V2 architecture whose primitive semantics are all-Nat information transport, three-space dynamics, exact information conservation, and finite-origin collision. The existing public theorem interfaces may remain temporarily as adapters, but no production proof may depend on the quarantined `h_creation_for_4pow`, the legacy residual Ω termination trio, or the old duality-wave ontology.

## Core ontology

1. **Information is never globally destroyed.** Local CREATE/DESTROY/SURVIVE/NEITHER labels are observational changes in a coordinate or space. Global information is preserved by exact ledgers and re-encoded across depth/space.
2. **The wave is three-space, not dual.** Production transport is modeled across NULL, ALT−, and GST+ spaces. Any legacy `gst_duality` theorem is demoted to an adapter/corollary.
3. **Termination is replaced by all-Nat control.** BIG-N and other finite-support statements describe support horizons inside a Nat-indexed object. They are not terminal proof axioms.
4. **Finite facts are projections of infinite control.** The new dependency direction is infinite controller -> arbitrary finite projection/collision, not repeated finite bounds -> infinity.
5. **Controlled chaos means exact invariants at every depth.** Complicated local transitions are allowed only while Ω additive conservation, Π/U origin conservation, canonical origin recurrences, and world/cardinal equations remain exact.

## Production dependency direction

```text
Mathlib
  -> GST V2 infinite core
  -> three-space transport / information ledgers / world control
  -> canonical origin control
  -> infinite finite-origin collision
  -> prefix-one navigation forcing
  -> residual navigation lift
  -> power-wave V2 / universal theorem
  -> ErdosTernary2 public compatibility surface
```

No production module may import the final monolith to prove a core invariant.

## Primary replacement seam

The immediate target is the current prefix-one seam, not `h_creation_for_4pow` itself:

```lean
theorem gst_v2_infinite_prefix_one_collision
    (s n : Nat) (hs : 1 <= s) (hn : 1 <= n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hbad : GSTOmegaInfiniteBadTrace s 1 n) : False
```

The production `gst_prefix_one_navigation_lift` should then close its contradiction branch by constructing `hbad` and applying this collision theorem. Downstream residual navigation must be rebuilt through `gst_residual_navigation_lift_of_prefix_one gst_prefix_one_navigation_lift` so the legacy residual Ω termination predicates disappear from the dependency graph.

## Stronger residual bridge

The preferred reusable forcing interface is the maximally 3-free residual bridge:

```lean
GSTCanonicalResidualInfiniteSupportBridge :=
  forall s n,
    1 <= s ->
    1 <= n ->
    n % 3 != 0 ->
    GSTNavigationWitness (gstNavigationConstant (s+1) n) ->
    GSTSeededBadTraceS 1 (z_s + A_s * gstNavigationConstant (s+1) n) ->
    InfiniteTernarySupportS n
```

A finite ordinary natural cannot have infinite ternary support, so the bridge is an immediate contradiction consumer. This theorem must be constructed from existing exact retained-state and infinite-control machinery; declaring the bridge as an abstract proposition is not a solution.

## Branch mechanics to preserve

- `n % 3 = 1`: first parent-tail digit is 0, event NEITHER, seed 1 -> 0; exact outer offset remains retained.
- `n % 3 = 2`: first parent-tail digit is 1, output 2 CREATE, seed remains 1; exact outer offset and multiplier remain retained.
- `n == 4 (mod 9)` with `s >= 2`: existing `Q_s(b) == 19 (mod 27)` cut yields a NULL Happy Gate at position 2.
- Terminal residual origin `n = 1`: use the already kernelized explicit/stable NULL terminal Happy Gate theorem, not a terminal-NULL assumption.
- All remaining branches must preserve the retained `(offset, multiplier, seed)` state and origin information until either a Happy Gate is forced or an all-depth finite-origin collision is obtained.

## New production layer boundaries

The upgrade should promote/refactor the strongest existing scratch theorems into focused production modules rather than duplicating them inside `ErdosTernary2.lean`:

- `GSTInfiniteCore.lean`: all-Nat digit/carry/path and support-horizon primitives.
- `GSTTriSpaceTransport.lean`: exact NULL/ALT−/GST+ transport semantics and compatibility lemmas for old duality consumers.
- `GSTInformationLedger.lean`: Ω Past/Future conservation plus Π/U retained-origin conservation.
- `GSTInfiniteWorldControl.lean`: cardinal/six-world all-scale equations and cofinal finite-origin collision tools.
- `GSTCanonicalOriginControl.lean`: retained offset recursion, residual NULL terminal/cylinder cuts, and canonical origin descent.
- `GSTInfiniteCollision.lean`: residual infinite-support bridge and prefix-one collision.
- `GSTPowerWaveV2.lean`: modern power transport/universal consumer; no dependency on quarantined `h_creation_for_4pow`.
- `GSTLegacyAdapters.lean`: temporary wrappers exposing legacy theorem names only when required by downstream consumers.

Existing scratch modules remain evidence/prototypes until their theorem bodies are promoted and kernel-checked in the production dependency direction.

## Legacy deprecations

Production must stop depending on:

- quarantined `h_creation_for_4pow` and its old oscillation chain;
- `gst_omega_termination_s1`;
- `gst_omega_termination_s3`;
- `gst_omega_termination_stable`;
- the circular bad-descend route through `gst_residual_omega_termination`;
- old `gst_duality` as a foundational theorem.

They may remain commented/quarantined during migration until the comparator is green.

## Verification contract

Every promoted theorem must pass:

```text
lake env lean <production module>
#print axioms <production theorem>
lake build
bash scripts/sorry_check.sh
bash scripts/comparator.sh
```

No `sorry`, `admit`, `sorryAx`, custom axioms, or `native_decide` proof escape is permitted in the production chain. The work is complete only when a fresh comparator run prints exactly:

```text
Your solution is okay!
COMPARATOR RESULT: PASS
```
