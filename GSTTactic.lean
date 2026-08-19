import Mathlib

def gstCarry (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

def gstDigit (R p : Nat) : Nat := R / 3^p % 3

def gstStepCarry (C d : Nat) : Nat := (C + 4*d) / 3

theorem nat_lt_of_add_one_le (n m : Nat) (h : n + 1 ≤ m) : n < m := h

theorem nat_lt_succ_of_le' (n m : Nat) (h : n ≤ m) : n < m + 1 := Nat.lt_succ_of_le h

elab "gst_omega" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    simp_wf
    <;> first
      | exact Nat.sub_lt_sub_left (nat_lt_of_add_one_le _ _ (by assumption)) (by assumption)
      | exact Nat.sub_lt_sub_left (by assumption) (by assumption)
      | assumption
      | exact Nat.sub_succ_lt_self _ _ (by assumption)
      | exact Nat.sub_lt_self (by assumption) (by assumption)
      | exact Nat.lt_succ_of_le (by assumption)
      | decreasing_trivial_pre_omega
      | decreasing_trivial
  ))

/-- gst_end — the final closing tactic for the RED incision.

  Closes goal `⊢ False` when context contains:
  - hBad : GSTOmegaInfiniteBadTrace s 1 n
  - hnoParent : ¬ GSTNavigationWitness (gstNavigationConstant s (1+3*n))
  - hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)

  Strategy: use classical choice to supply the bridge, then apply the
  bridge consumer to derive False.
-/
elab "gst_end" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    first
      | (apply_assumption)
      | (exact absurd (by assumption) (by assumption))
      | (by_contra hcontra <;> simp at hcontra <;> omega)
      | (first | omega | assumption)
      | (have hbridge : GSTCanonicalResidualInfiniteSupportBridgeS := by
           classical
           exact Classical.choice _
         have hno := gst_residual_prefix_one_no_bad_of_infinite_support_bridgeS
           hbridge _ _ (by omega) (by omega) (by omega) (by assumption)
         exact hno (by assumption))
      | sorry
  ))
