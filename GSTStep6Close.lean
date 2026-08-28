import GSTPrefixOnePhaseIncidenceControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open Lean Meta Elab Tactic

namespace GSTStep6Close

private def headConst? (e : Expr) : MetaM (Option Name) := do
  let e ← whnf e
  return e.getAppFn.constName?

private def findHypWithHead (goal : MVarId) (head : Name) : MetaM (Option FVarId) :=
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      if (← headConst? localDecl.type) == some head then
        return some localDecl.fvarId
    return none

private def requireHypWithHead (goal : MVarId) (head : Name) (label : String) : MetaM FVarId := do
  match ← findHypWithHead goal head with
  | some fvar => pure fvar
  | none => throwError "gst_step6_close: required semantic packet not found: {label}"

/--
`gst_step6_close` is the dedicated semantic closer for the prefix-one Step-6
collision.  It does not spray generic automation over the local context.

The tactic first checks that the two proof-critical inputs are actually present
by type: a child `GSTNavigationWitness` and the all-depth parent
`GSTOmegaInfiniteBadTrace`.  It then exposes the certified exact-gate phase
packet and asks the arithmetic kernel to close only after those semantic facts
have been materialized.

This first standalone implementation intentionally fails loudly if the
remaining phase-incidence relation is not sufficient; that failure is the TDD
frontier for the next kernel lemma rather than a hidden `aesop` search.
-/
elab "gst_step6_close" : tactic => do
  let goal ← getMainGoal
  let _ ← requireHypWithHead goal ``GSTNavigationWitness "child GSTNavigationWitness"
  let _ ← requireHypWithHead goal ``GSTOmegaInfiniteBadTrace "parent GSTOmegaInfiniteBadTrace"
  evalTactic (← `(tactic|
    first
      | contradiction
      | (obtain ⟨q, hChord, hZeroPhase⟩ :=
            gpt56_prefix_one_zero_phase_forces_next_escape
              _ _ (by assumption) (by assumption) (by assumption) (by assumption)
         have hPhaseTable :=
            gpt56_prefix_one_exact_gate_three_phase_table
              _ _ (by assumption) (by assumption) (by assumption) (by assumption)
         have hPast :=
            gpt56_prefix_one_exact_gate_past_incidence
              _ _ (by assumption) (by assumption) (by assumption) (by assumption)
         first
           | omega
           | fail "gst_step6_close: semantic packet extracted; missing final phase/controller conservation relation")
  ))

end GSTStep6Close
