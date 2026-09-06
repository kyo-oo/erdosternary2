# GST Module Map

This document groups the Lean modules by mathematical role. It is a reviewer map, not a replacement for the Lean source.

## Core source artifact

| Module/file | Role |
|---|---|
| `ErdosTernary2.lean` | Preserved monolith proof artifact imported by the comparator-facing solution and public wrapper layer. |
| `questions/deepmind_problem_406/Challenge.lean` | Benchmark statement surface with the intentional challenge-side hole. |
| `questions/deepmind_problem_406/Solution.lean` | Comparator-facing solution bridge importing the accepted monolith theorem. |
| `GST/Problem406/PublicAPI.lean` | Clean public theorem alias layer around the accepted theorem. |
| `GST/Problem406/TheoremMap.lean` | Compile-checked index of the public Problem 406 surface. |

## GST core and tactics

| Module/file | Role |
|---|---|
| `GSTTactic.lean` | Local arithmetic helpers and GST-specific tactics such as carry/digit case tactics, `gst_omega`, and `gst_end`. |
| `GSTCanonicalTailStateIso.lean` | Defines `digit3`, `carry4`, `HappyCell`, `Navigation`, and canonical tail state isomorphism. |
| `GSTCanonicalCarryDynamics.lean` | Basic carry bounds and exact carry regeneration laws. |
| `GSTCanonicalSevenAxisBridge.lean` | Seven-axis vertex/carry/digit bridge layer used by Graph V2. |
| `GSTCanonicalTailLTE.lean` | Canonical tail/LTE support layer. |

## Two-dimensional emergence and U2D

| Module/file | Role |
|---|---|
| `GST2DMixedEmergence.lean` | Defines microscopic x2/x4 dynamics, U charge, seven-kernel, mixed density, and the mixed rectangle emergence theorem. |
| `GSTU2DAtomicBridge.lean` | Atomic U-to-D bridge support. |
| `GSTU2DEventTransport.lean` | Event transport layer. |
| `GSTU2DExactCrossingCharge.lean` | Exact crossing-charge definitions and base inequalities. |
| `GSTU2DSharpCrossingBlock.lean` | Sharp crossing bounds and highest-Happy-row domination. |
| `GSTU2DCanonicalPhaseDensity.lean` | Canonical phase-density support. |
| `GSTU2DPureDivergence83.lean` | Independent 8x3 density/divergence support. |

## GST Graph V2

| Module/file | Role |
|---|---|
| `GSTGraphV2Production.lean` | Main production graph object: cells, sheets, lattices, rectangles, origin frames, residual frames, and canonical cut frames. |
| `GSTGraphV2ProductionLaws.lean` | Production graph laws: horizontal x4 edge, vertical ternary edge, nullspace flux, origin phasing, residual gate laws. |
| `GSTGraphV2InfiniteControl.lean` | All-depth graph control layer. |
| `GSTGraphV2InfiniteControllerBridge.lean` | Bridge between Graph V2 infinite controller and production proof layers. |
| `GSTGraphV2PerfectPowerBlockProbe.lean` | Perfect-power block probe used by the monolith import stack. |
| `GSTGraphV2Canonical*` modules | Canonical descent, escape, phase, renormalization, sheet translation, terminal extinction, and infinite-cycle layers. |
| `GSTGraphV2Handwritten*` modules | Handwritten exponential/LTE/cocycle/omega-U-block source layers. |
| `GSTGraphV2SixAdic*` modules | Six-adic geometry, laws, synchronized shadows, and unit isometry. |

## Four-power direct arithmetic

| Module/file | Role |
|---|---|
| `GSTFourPowerDirectResidue.lean` | Base four-power arithmetic: ternary digit, LTE coefficient, exponent periodicity, row-two classifier. |
| `GSTFourPowerDirectResidue27.lean` | Row-three modulo 27 classifier. |
| `GSTFourPowerDirectResidue81.lean` | Row-four modulo 81 classifier. |
| `GSTFourPowerDirectAdditionCarry.lean` | Direct addition/carry mechanics for multiplication by four. |
| `GSTFourPowerDirectNo22.lean` | No-common-two consequences, especially exclusion of adjacent `22` source blocks. |
| `GSTFourPowerNo22Magnitude.lean` | Magnitude/support layer for no-`22` analysis. |
| `GSTFourPowerExponentTritObstruction.lean` | Exponent prefix/trit decomposition and parametric obstruction law. |
| `GSTFinalPurePowerResidueTransplant.lean` | Transplanted pure-power residue and strip-conservation arithmetic. |

## Affine channels and Chat-2 realization

| Module/file | Role |
|---|---|
| `GSTFourPowerAffineBadState.lean` | Bad-state language for affine/common-two failure. |
| `GSTFourPowerAffineChannelAutomaton.lean` | Finite ternary affine transducer: `BadChannel`, split laws, and channel recursion. |
| `GSTFourPowerAffineOrbit.lean` | Affine orbit of the exponent. |
| `GSTFourPowerAffineExponentPeel.lean` | Exponent peeling layer. |
| `GSTFourPowerAffineClassifierBridge.lean` | Classifier bridge between direct and affine forms. |
| `GSTFourPowerAffinePeelClassifier.lean` | Peeling classifier layer. |
| `GSTFourPowerAffineTwoTritClassifier.lean` | Two-trit classifier layer. |
| `GSTFourPowerDirectChat2Application.lean` | Chat-2 application surface: equivalence between direct common-two failure and bad affine channel `B₁`. |

## Provider and certificate pipeline

| Module/file | Role |
|---|---|
| `GSTFourPowerDirectExistence.lean` | Defines `CommonTwo` and `FourPowerDirectExistence`, plus direct obstruction bundle components. |
| `GSTFourPowerHappyProvider.lean` | Row-three-or-higher Happy/CommonTwo provider layer. |
| `GSTFourPowerDirectHappyBridge.lean` | Direct-to-Happy bridge layer. |
| `GSTFourPowerDirectExistenceNoAxiom.lean` | Isolated no-axiom bridge target. |
| `GSTFourPowerDirectExistenceProviderPipeline.lean` | Provider gates and no-axiom routes into direct existence and creation certificates. |
| `GSTFourPowerDirectCreationMaster.lean` | Direct existence to creation master. |
| `GSTFourPowerOntologicalAdapter.lean` | Creation certificate to Navigation adapter. |
| `GSTPrefixOneOntologicalEscape.lean` | Prefix-one escape plus no-axiom transplant entrypoints and the explicit legacy compatibility boundary. |

## Infinite transport and prefix-one families

| Module/file | Role |
|---|---|
| `GSTV2InfiniteCore.lean` | Core all-depth infinite-state definitions. |
| `GSTInfiniteCollision.lean` | Coupled all-depth information transport and invariant preservation. |
| `GSTInfiniteBadTransport.lean` | Bad-state transport layer. |
| `GSTInfiniteCoupledLedger.lean` | Coupled ledger bookkeeping. |
| `GSTInfiniteGateTransport.lean` | Gate transport layer. |
| `GSTPerfectPowerTailNavigation.lean` | Perfect-power tail navigation. |
| `GSTPrefixOneSeedCore.lean` | Prefix-one seed core. |
| `GSTPrefixOneU2DCollisionProof.lean` | Prefix-one/U2D collision proof layer imported by the monolith. |
| `GSTStep6Close.lean`, `GSTStep6CollisionKernel.lean` | Historical step-six closure/kernel layer; should be indexed but not promoted as public naming style. |
