import GSTStep6CollisionKernel
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
The production Step-6 closer.

This tactic deliberately imports the certified collision kernel instead of
trying to remain theorem-free.  The previous dependency-free wrapper could
locate the semantic packets, but its delayed unqualified `apply` call was too
fragile in CI and failed exactly at the regression seam.  Here the kernel is a
real imported constant, and the final closure is theorem-backed by
`_root_.gst_step6_collision_kernel`.
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
      | (exact _root_.gst_step6_collision_kernel _ _ (by assumption) (by assumption) (by assumption) (by assumption))
      | (apply _root_.gst_step6_collision_kernel <;> assumption)
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
