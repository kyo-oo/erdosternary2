import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open Lean Meta Elab Tactic

namespace GSTStep6Close

private def headConst? (e : Expr) : MetaM (Option Name) := do
  -- Preserve the proposition's semantic wrapper.  Reducing first unfolds
  -- transparent packet definitions (including the production wrappers) and
  -- loses the declaration name that the tactic is meant to recognize.
  pure e.getAppFn.constName?

private def nameEndsWith (n : Name) (suffix : String) : Bool :=
  n.toString == suffix || n.toString.endsWith ("." ++ suffix)

private def findHypWithHeadSuffix
    (goal : MVarId) (suffix : String) : MetaM (Option FVarId) :=
  goal.withContext do
    for localDecl in ← getLCtx do
      if !localDecl.isImplementationDetail then
        match ← headConst? localDecl.type with
        | some head =>
            if nameEndsWith head suffix then
              return some localDecl.fvarId
        | none => pure ()
    pure none

private def requireHypWithHeadSuffix
    (goal : MVarId) (suffix label : String) : MetaM FVarId := do
  match ← findHypWithHeadSuffix goal suffix with
  | some fvar => pure fvar
  | none =>
      throwError "gst_step6_close: required semantic packet not found: {label}"

/--
Dependency-free metaprogramming kernel for the prefix-one Step-6 closer.

The proof mathematics is intentionally *not* imported here.  This keeps the
custom tactic usable from the production monolith without creating a circular
proof dependency.  Semantic packets are discovered by the head constant of
their types, not by fragile local hypothesis names.

The closing pipeline is deliberately conservative: direct contradiction and
Presburger closure are tried first, then the importing proof layer's certified
`gst_step6_collision_kernel` theorem is applied.  The theorem name is resolved
at tactic invocation time, so this metaprogramming kernel remains independent
of the production monolith and cannot introduce an import cycle.
-/
elab "gst_step6_close" : tactic => do
  let goal ← getMainGoal
  let _ ← requireHypWithHeadSuffix goal
    "GSTNavigationWitness" "child GSTNavigationWitness"
  let _ ← requireHypWithHeadSuffix goal
    "GSTOmegaInfiniteBadTrace" "parent GSTOmegaInfiniteBadTrace"
  evalTactic (← `(tactic|
    first
      | contradiction
      | omega
      | (apply gst_step6_collision_kernel <;> assumption)
      | fail "gst_step6_close: semantic packets found; certified gst_step6_collision_kernel was not applicable"))

/-- Diagnostic form used while developing the semantic reducer.  It verifies
that the tactic can locate both production packets without attempting closure. -/
elab "gst_step6_packets" : tactic => do
  let goal ← getMainGoal
  let _ ← requireHypWithHeadSuffix goal
    "GSTNavigationWitness" "child GSTNavigationWitness"
  let _ ← requireHypWithHeadSuffix goal
    "GSTOmegaInfiniteBadTrace" "parent GSTOmegaInfiniteBadTrace"
  logInfo "gst_step6_packets: child Navigation + parent all-depth badness located"

end GSTStep6Close
