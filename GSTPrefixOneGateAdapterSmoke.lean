import GSTPrefixOneInfiniteAdapterSmoke

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTV2

/-- A monolith Navigation witness gives the exact carry/digit Happy cell used
by the independent V2 controller. -/
theorem gpt56_navigation_witness_to_v2_happy
    (Q : Nat) (hnav : GSTNavigationWitness Q) :
    ∃ j, GSTV2.Happy (GSTV2.naturalCarry Q j) (GSTV2.digit Q j) := by
  obtain ⟨j, hd, hspace⟩ := hnav
  have hC : gstCarry Q j = 0 ∨ gstCarry Q j = 3 := by
    cases j with
    | zero =>
        left
        simp [gstCarry]
    | succ j =>
        have hmod : gstCarry Q (j+1) % 3 = 0 :=
          gstGoodSpace_carry_mod3_zero Q (j+1) hspace
        have hlt : gstCarry Q (j+1) < 4 :=
          gstCarry_lt_four Q (j+1) (by omega)
        omega
  refine ⟨j, ?_⟩
  constructor
  · simpa [GSTV2.digit, gstDigit] using hd
  · simpa [GSTV2.naturalCarry, gstCarry] using hC

/-- The certified child Happy Gate is realized inside the *same* all-depth
coupled controller that carries the complete parent bad language. -/
theorem gpt56_prefix_one_controller_realizes_child_gate
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ∃ j,
      GSTV2.Happy
        (GSTV2.coupledOrbit (gpt56PrefixOneA s)
          (gpt56PrefixOneInitialState s n) j).childCarry
        ((GSTV2.coupledOrbit (gpt56PrefixOneA s)
          (gpt56PrefixOneInitialState s n) j).childTail % 3) := by
  let initial := gpt56PrefixOneInitialState s n
  let A := gpt56PrefixOneA s
  have hcontrol := gpt56_prefix_one_infinite_bad_control s n hs hBad
  obtain ⟨j, hHappy⟩ :=
    gpt56_navigation_witness_to_v2_happy
      (gstNavigationConstant (s+1) n) hchild
  refine ⟨j, ?_⟩
  have hCarry := hcontrol.childCarryExact j
  have hDigit := GSTV2.coupledOrbit_childDigit_exact A initial j
  dsimp [A, initial] at hCarry hDigit ⊢
  rw [hCarry, hDigit]
  exact hHappy

/-- Exact synchronized collision state at the certified child gate: child is
Happy, parent is locally bad, the complete parent bad suffix remains present,
and the shared two-endpoint conservation equation still holds. -/
structure GPT56PrefixOneGateCollisionState
    (s n j : Nat) : Prop where
  childHappy :
    GSTV2.Happy
      (GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j).childCarry
      ((GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j).childTail % 3)
  parentBad :
    ¬ GSTV2.Happy
      (GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j).parentSeed
      (((GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j).parentOffset +
        gpt56PrefixOneA s *
          ((GSTV2.coupledOrbit (gpt56PrefixOneA s)
            (gpt56PrefixOneInitialState s n) j).childTail % 3)) % 3)
  sharedInvariant :
    GSTV2.CoupledInvariant (gpt56PrefixOneA s)
      (GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j)
  parentBadSuffix :
    GSTV2.SeededBadTrace
      (GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j).parentSeed
      ((GSTV2.coupledOrbit (gpt56PrefixOneA s)
        (gpt56PrefixOneInitialState s n) j).parentWord (gpt56PrefixOneA s))

/-- A child Navigation witness plus parent Ω badness constructs the exact
four-coordinate collision state, with no appeal to legacy Ω termination. -/
theorem gpt56_prefix_one_gate_collision_state
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ∃ j, GPT56PrefixOneGateCollisionState s n j := by
  have hcontrol := gpt56_prefix_one_infinite_bad_control s n hs hBad
  obtain ⟨j, hchildHappy⟩ :=
    gpt56_prefix_one_controller_realizes_child_gate s n hs hBad hchild
  refine ⟨j, ?_⟩
  constructor
  · exact hchildHappy
  · exact GSTV2.coupledOrbit_parent_bad_current
      (gpt56PrefixOneA s) (gpt56PrefixOneInitialState s n)
      hcontrol.parentBad j
  · exact hcontrol.coupled.invariantAll j
  · exact hcontrol.parentBadSuffix j

#print axioms gpt56_navigation_witness_to_v2_happy
#print axioms gpt56_prefix_one_controller_realizes_child_gate
#print axioms gpt56_prefix_one_gate_collision_state
