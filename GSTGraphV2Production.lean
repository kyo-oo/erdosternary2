import GSTGraphV2HandwrittenAnchoredCocycle
import GSTU2DCanonicalPhaseDensity
import GSTU2DPureDivergence83

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Production

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2CoupledUFlux
open GSTGraphV2CoupledUPhysicalBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2HandwrittenExponentialCascade
open GSTGraphV2HandwrittenAnchoredCocycle
open GSTGraphV2PerfectPowerBlock
open GSTU2DCanonicalPhaseDensity
open GSTU2DPureDivergence83

/-!
# GST Graph V2 — production object

This file constructs the one graph object that all later production mathematics
must use.  It deliberately introduces no closing theorem and no alternative
surrogate graph.

The underlying sheet remains the already-defined all-depth arithmetic graph
`GSTGraphV2InfiniteControl.graph E t p`.  This module only assembles all of its
currently-green coordinates into one explicit production state:

* the canonical seven arithmetic axes and physical GST space;
* event, U, mixed, crossing and SURVIVE observables;
* the exact local U jump;
* the Equation-I navigation/nullspace residue;
* canonical phase density and the independent 8x3 density;
* finite horizontal rectangle state on the same infinite sheet;
* exact natural-origin prefix/suffix/phase coordinates on the same sheet;
* the generalized residual `(s,k,m)` frame used by the production seam;
* the canonical production-cut frame at `p = s+2+q`.

No finite rectangle replaces the infinite graph.  Rectangles and origin frames
below are observations/re-coordinatizations of the same absolute energy.
-/

/-- One complete production cell of GST Graph V2. -/
structure Cell where
  sourceEnergy : Nat
  horizontal : Nat
  vertical : Nat
  absoluteEnergy : Nat
  seven : GSTCanonicalSevenAxisBridge.Vertex
  eventCode : Nat
  uCharge : Int
  uJump : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  navigationNullspace : Nat
  phaseDensity : Int
  density83 : Int
  deriving Repr

/-- Assemble every currently-green local observable at one point of the single
infinite GST Graph V2 sheet. -/
def cell (E t p : Nat) : Cell :=
  let g := GSTGraphV2InfiniteControl.graph E t p
  let R := 4^t * E
  {
    sourceEnergy := E
    horizontal := t
    vertical := p
    absoluteEnergy := R
    seven := g.seven
    eventCode := g.eventCode
    uCharge := g.uCharge
    uJump := GSTGraphV2CoupledUFlux.gstUJumpExact g.seven.carry g.seven.digit
    mixedCharge := g.mixedCharge
    crossingCharge := g.crossingCharge
    survive := g.survive
    navigationNullspace :=
      GSTGraphV2HandwrittenExponentialCascade.navigationNullspace R p
    phaseDensity := GSTU2DCanonicalPhaseDensity.phaseDensity
      g.seven.carry g.seven.digit
    density83 := GSTU2DPureDivergence83.density83
      g.seven.carry g.seven.digit
  }

/-- The production graph is genuinely infinite in both arithmetic coordinates. -/
abbrev Sheet := Nat → Nat → Cell

def graph (E : Nat) : Sheet := fun t p => cell E t p

/-- Explicit local neighborhood of one production cell.  Horizontal means one
exact x4 step; vertical means one exact base-three information step. -/
structure Neighborhood where
  center : Cell
  horizontalNext : Cell
  verticalNext : Cell
  deriving Repr

def neighborhood (E t p : Nat) : Neighborhood :=
  {
    center := cell E t p
    horizontalNext := cell E (t+1) p
    verticalNext := cell E t (p+1)
  }

/-- A finite horizontal observation of the one infinite graph.  It retains the
literal endpoint cells, the base-four carry word, the old coupled physical
state and the direct U potential. -/
structure Rectangle where
  sourceEnergy : Nat
  width : Nat
  vertical : Nat
  left : Cell
  right : Cell
  carryWord : Nat
  physical : GSTGraphV2CoupledUPhysicalBridge.PhysicalState
  uPotential : Int
  deriving Repr

/-- Width-N production rectangle beginning at horizontal coordinate zero. -/
def rectangle (E N p : Nat) : Rectangle :=
  {
    sourceEnergy := E
    width := N
    vertical := p
    left := cell E 0 p
    right := cell E N p
    carryWord := GSTGraphV2UnifiedPowerRectangle.carryWord E p 0 N
    physical := GSTGraphV2UnifiedPowerRectangle.unifiedState E N p
    uPotential := GSTGraphV2HandwrittenAnchoredCocycle.graphUPotential E 0 N p
  }

/-- Exact natural-origin coordinates used by the handwritten U operation.
This is data only: no limit and no terminal-space interpretation is added. -/
structure OriginCoordinates where
  level : Nat
  origin : Nat
  depth : Nat
  prefix : Nat
  suffix : Nat
  phaseShift : Nat
  tailExponent : Nat
  tailEnergy : Nat
  deriving Repr

/-- Consume exactly `K` ternary origin trits into the horizontal phase. -/
def originCoordinates (t n K : Nat) : OriginCoordinates :=
  {
    level := t
    origin := n
    depth := K
    prefix := GSTGraphV2HandwrittenExponentialCascade.originPrefix n K
    suffix := GSTGraphV2HandwrittenExponentialCascade.originSuffix n K
    phaseShift := GSTGraphV2HandwrittenExponentialCascade.uPhaseShift t n K
    tailExponent := GSTGraphV2HandwrittenExponentialCascade.uTailExponent t n K
    tailEnergy := GSTGraphV2HandwrittenExponentialCascade.uTailEnergy t n K
  }

/-- One full re-coordinatized observation of a perfect-power origin.  The
`full` and `tail` cells are stored simultaneously; later proofs must identify
them through the existing exact transport laws rather than by replacing either
side with a surrogate. -/
structure OriginFrame where
  coordinates : OriginCoordinates
  horizontalOffset : Nat
  vertical : Nat
  fullEnergy : Nat
  full : Cell
  tail : Cell
  deriving Repr

/-- Build the `K`-trit origin frame at arbitrary horizontal/vertical location. -/
def originFrame (t n K x p : Nat) : OriginFrame :=
  let o := originCoordinates t n K
  {
    coordinates := o
    horizontalOffset := x
    vertical := p
    fullEnergy := 4^(3^t * n)
    full := cell (4^(3^t * n)) x p
    tail := cell o.tailEnergy (o.phaseShift + x) p
  }

/-- Canonical production energy for the prefix-one problem. -/
def canonicalEnergy (s n : Nat) : Nat :=
  GSTGraphV2PerfectPowerBlock.canonicalEnergy s n

/-- Exact one-parent-block horizontal width. -/
def canonicalWidth (s : Nat) : Nat :=
  GSTGraphV2PerfectPowerBlock.canonicalWidth s

/-- The canonical prefix-one sheet as an instance of the single production graph. -/
def canonicalGraph (s n : Nat) : Sheet := graph (canonicalEnergy s n)

/-- Canonical parent-block rectangle at a vertical observation coordinate. -/
def canonicalRectangle (s n p : Nat) : Rectangle :=
  rectangle (canonicalEnergy s n) (canonicalWidth s) p

/-- Residual perfect-power energy in generalized `(s,k,m)` coordinates. -/
def residualEnergy (s k m : Nat) : Nat :=
  GSTGraphV2HandwrittenOmegaUBlock.residualEnergy s k m

/-- Residual sheet, still the same production graph object. -/
def residualGraph (s k m : Nat) : Sheet := graph (residualEnergy s k m)

/-- Residual one-parent-block rectangle, with no collision assertion attached. -/
def residualRectangle (s k m p : Nat) : Rectangle :=
  rectangle (residualEnergy s k m)
    (GSTGraphV2HandwrittenOmegaUBlock.residualWidth s) p

/-- Complete generalized residual coordinates.  This stores both exponent
labels and the exact physical rectangle on which the later residual argument
must operate. -/
structure ResidualFrame where
  s : Nat
  k : Nat
  origin : Nat
  vertical : Nat
  childExponent : Nat
  parentExponent : Nat
  childEnergy : Nat
  parentWidth : Nat
  originTrit : Nat
  originTail : Nat
  nextTailEnergy : Nat
  block : Rectangle
  deriving Repr

/-- Build the actual `(s,k,m)` residual production frame without making any
termination or collision claim. -/
def residualFrame (s k m p : Nat) : ResidualFrame :=
  {
    s := s
    k := k
    origin := m
    vertical := p
    childExponent := GSTGraphV2HandwrittenOmegaUBlock.residualChildExponent s k m
    parentExponent := GSTGraphV2HandwrittenOmegaUBlock.residualParentExponent s k m
    childEnergy := residualEnergy s k m
    parentWidth := GSTGraphV2HandwrittenOmegaUBlock.residualWidth s
    originTrit := GSTGraphV2HandwrittenOmegaUBlock.originTrit m
    originTail := GSTGraphV2HandwrittenOmegaUBlock.originTail m
    nextTailEnergy := 4^(3^(s+k+1) * GSTGraphV2HandwrittenOmegaUBlock.originTail m)
    block := residualRectangle s k m p
  }

/-- Canonical row used by the production prefix-one seam. -/
def canonicalCutRow (s q : Nat) : Nat := s + 2 + q

/-- The exact canonical cut packet.  It contains the physical parent block and
the corresponding `q+1`-trit U re-coordinatization simultaneously. -/
structure CanonicalCutFrame where
  s : Nat
  origin : Nat
  gateDepth : Nat
  row : Nat
  energy : Nat
  width : Nat
  block : Rectangle
  uFrame : OriginFrame
  deriving Repr

/-- Build the production cut at the exact row `s+2+q`. -/
def canonicalCutFrame (s n q : Nat) : CanonicalCutFrame :=
  let p := canonicalCutRow s q
  {
    s := s
    origin := n
    gateDepth := q
    row := p
    energy := canonicalEnergy s n
    width := canonicalWidth s
    block := canonicalRectangle s n p
    uFrame := originFrame (s+1) n (q+1) 0 p
  }

#check Cell
#check graph
#check Neighborhood
#check neighborhood
#check Rectangle
#check rectangle
#check OriginCoordinates
#check originCoordinates
#check OriginFrame
#check originFrame
#check canonicalGraph
#check canonicalRectangle
#check residualGraph
#check residualRectangle
#check ResidualFrame
#check residualFrame
#check CanonicalCutFrame
#check canonicalCutFrame

end GSTGraphV2Production
