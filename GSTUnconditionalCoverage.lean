import ErdosTernary2
import GSTGraphV2OmegaWaveLaw
import GSTShadowSeparationAttack
import GSTShadowGapReceipt

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# THE UNCONDITIONAL COVERAGE — the gates, paid and stated

The campaign's discovery agents inventoried every theorem in the monolith
and its supporting modules.  The finding: the dispatch behind
`four_power_omega_shadow_wave_of_tailF` (ErdosTernary2.lean) pays FIVE
unconditional gates inside its proof body — the kernel-checked base, the
sheet gate, both second-sheet gates, the uniform all-depths row law, and
the uniform all-levels tower law — but no single theorem ever exposed
that content with the input consumed.  Meanwhile the shadow separation
attack's level-five kernel receipt (`separation_level_five`, 211 of 243
residue classes killed) sits compiled and green while imported by
nothing.

This module is the combination: one hypothesis-free dichotomy for every
shadow exponent, one maximal unconditional coverage theorem for the full
crown statement, and the smallest named residual object the campaign has
ever reduced the war to — `CombinedResidual`.

The main statements:

* `shadow_split_of_gates` — every shadow exponent from eight on either
  satisfies the complete second-observer tailF package or owns a ternary
  digit two, with zero input.
* `erdos_ternary_2_unconditional_coverage` — the full Erdős ternary-two
  statement for every `n ≥ 9` whose half-exponent is: bounded by the
  kernel base, or outside the tailF package, or in one of the 211 killed
  level-five classes, or in the elementary mod-three / mod-nine classes.
* `erdos_ternary_2_iff_combined_residual` — the full crown is equivalent
  to the combined residual family firing: `500 < K`, the complete tailF
  package, and a level-five surviving class.
-/

namespace GSTUnconditionalCoverage

/-! ## The shadow dichotomy, input consumed -/

/-- **THE SHADOW DICHOTOMY.**  Every shadow exponent from eight on: either
the full second-observer tailF package holds for it (every gate window
clean), or it owns a ternary digit two — with no input at all.  This is
the dispatch of `four_power_omega_shadow_wave_of_tailF` with the tail
input consumed: the case tree is identical, and the final branch returns
the tailF witnesses instead of invoking the hypothesis. -/
theorem shadow_split_of_gates (K : Nat) (hK : 8 ≤ K)
    (hShadow : GSTGraphV2OmegaWaveLaw.omegaShadow K) :
    GSTGraphV2OmegaWaveLaw.omegaShadowTailF K ∨
      ∃ p : Nat, (4 ^ K) / 3 ^ p % 3 = 2 := by
  by_cases h500 : K ≤ 500
  · obtain ⟨q, hq, _⟩ :=
      hasTernaryTwo_first_pos (4 ^ K) (modular_check_base K (by omega) h500)
    exact Or.inr ⟨q, hq⟩
  · obtain ⟨s, core, hsc, hc3, hsheet⟩ := hShadow
    by_cases hSG :
        2 * 3 ^ (s + 1) ≤ (GSTGraphV2OmegaWaveLaw.omegaCutWord s core) % 3 ^ (s + 2)
    · have hc1 : core % 3 = 1 := by
        rcases hsheet with h4 | ⟨_, h1⟩ | ⟨_, h7⟩ <;> omega
      rw [hsc]
      exact Or.inr ⟨2 * s + 2,
        GSTGraphV2OmegaWaveLaw.omega_sheet_gate_digit_two s core hc1 hSG⟩
    · by_cases hS2 : 1 ≤ s ∧
          ((core % 9 = 4 ∧ (GSTFourPowerDirectResidue.lteCoeff s * core)
              % 3 ^ (s + 3) < 3 ^ (s + 2))
          ∨ (core % 9 = 7 ∧ 3 ^ (s + 2)
              ≤ (GSTFourPowerDirectResidue.lteCoeff s * core) % 3 ^ (s + 3)
            ∧ (GSTFourPowerDirectResidue.lteCoeff s * core) % 3 ^ (s + 3)
              < 2 * 3 ^ (s + 2)))
      · obtain ⟨hs1, hclass⟩ := hS2
        rcases hclass with ⟨h4c, hq4⟩ | ⟨h7c, hq7, hq7'⟩
        · rw [hsc]
          exact Or.inr ⟨2 * s + 3,
            GSTGraphV2OmegaWaveLaw.omega_sheet2_gate_four s core hs1 h4c hq4⟩
        · rw [hsc]
          exact Or.inr ⟨2 * s + 3,
            GSTGraphV2OmegaWaveLaw.omega_sheet2_gate_seven s core hs1 h7c hq7 hq7'⟩
      · by_cases hRow : s = 0 ∧ ∃ j : Nat, 2 ≤ j ∧
            2 * 3 ^ j ≤ (GSTGraphV2OmegaWaveLaw.omegaCutWord 0 core) % 3 ^ (j + 1)
        · obtain ⟨hs0, j, hj, hkill⟩ := hRow
          have hKc : K = core := by
            rw [hsc, hs0, Nat.pow_zero, Nat.one_mul]
          rw [hKc]
          exact Or.inr ⟨1 + j,
            GSTGraphV2OmegaWaveLaw.omega_row_level_digit_two core j hkill⟩
        · by_cases hTower : ∃ k : Nat, 3 ≤ k ∧ k ≤ s + 1 ∧
            2 * 3 ^ (k - 1) ≤
              (GSTGraphV2OmegaWaveLaw.omegaCutWord s 1 * core) % 3 ^ k
          · obtain ⟨k, hk3, hks, hkg⟩ := hTower
            refine Or.inr ⟨s + k, ?_⟩
            rw [hsc]
            exact GSTGraphV2OmegaWaveLaw.omega_tower_level_digit_two
              s core k hk3 hks hkg
          · refine Or.inl ⟨s, core, hsc, hc3, hsheet, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · intro hs1 h4c
              rcases Nat.lt_or_ge
                  (GSTFourPowerDirectResidue.lteCoeff s * core % 3 ^ (s + 3))
                  (3 ^ (s + 2)) with hlt | hge
              · exact absurd ⟨hs1, Or.inl ⟨h4c, hlt⟩⟩ hS2
              · exact hge
            · intro hs1 h7c
              rcases Nat.lt_or_ge
                  (GSTFourPowerDirectResidue.lteCoeff s * core % 3 ^ (s + 3))
                  (3 ^ (s + 2)) with hlt | hge
              · exact Or.inl hlt
              · refine Or.inr ?_
                by_cases hlt2 :
                    (GSTFourPowerDirectResidue.lteCoeff s * core % 3 ^ (s + 3))
                      < 2 * 3 ^ (s + 2)
                · exact absurd ⟨hs1, Or.inr ⟨h7c, hge, hlt2⟩⟩ hS2
                · omega
            · intro hs0 j hj
              by_contra hge
              exact absurd ⟨hs0, j, hj, by omega⟩ hRow
            · intro k hk3 hks
              exact Nat.lt_of_not_ge (fun hge =>
                hTower ⟨k, hk3, hks, hge⟩)

/-! ## The maximal unconditional coverage -/

/-- **THE MAXIMAL UNCONDITIONAL COVERAGE.**  The full Erdős ternary-two
statement holds for every `n ≥ 9` whose half-exponent `n / 2` satisfies
any ONE of: the kernel base bound `n / 2 ≤ 500`; the negation of the
complete second-observer tailF package (so one of the five gates —
sheet, second-sheet, row, tower, or base — fires it); membership in one
of the 211 killed level-five residue classes; or the elementary
mod-three / mod-nine digit classes.  Every route to the crown that the
campaign has ever paid is folded into this one statement with zero
input. -/
theorem erdos_ternary_2_unconditional_coverage (n : Nat) (hn : 9 ≤ n)
    (hcov : n % 2 = 1 ∨ n / 2 ≤ 500 ∨
      ¬ GSTGraphV2OmegaWaveLaw.omegaShadowTailF (n / 2) ∨
      GSTShadowSeparationAttack.survivor5 (n / 2 % 243) = false ∨
      n / 2 % 3 = 2 ∨ n / 2 % 9 = 7) :
    noTernaryTwo (2 ^ n) = false := by
  by_cases hodd : n % 2 = 1
  · exact erdos_ternary_2_odd_universal n hn hodd
  · have h4eq : 2 ^ n = 4 ^ (n / 2) := by
      have hn_eq : n = 2 * (n / 2) := by omega
      rw [show (4 : Nat) = 2 ^ 2 from by decide, ← Nat.pow_mul, ← hn_eq]
    rw [h4eq]
    refine has_two_imp_not_no_two (4 ^ (n / 2)) ?_
    rcases hcov with h | h | h | h | h | h
    · exact absurd h hodd
    · exact modular_check_base (n / 2) (by omega) h
    · by_cases h500 : n / 2 ≤ 500
      · exact modular_check_base (n / 2) (by omega) h500
      · have hK8 : 8 ≤ n / 2 := by omega
        rcases GSTGraphV2OmegaWaveLaw.omega_digit_two_cases (n / 2) hK8 with
          hShadow | ⟨p, hp⟩
        · rcases shadow_split_of_gates (n / 2) hK8 hShadow with hT | ⟨p, hp⟩
          · exact absurd hT h
          · exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
        · exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
    · obtain ⟨p, _, hp⟩ :=
        GSTShadowSeparationAttack.separation_level_five (n / 2) h
      exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
    · exact even_case_a_mod3_2 (n / 2) h
    · exact even_case_a_7_mod9 (n / 2) h

/-! ## The combined residual — the war's smallest named object -/

/-- **THE COMBINED RESIDUAL.**  The half-exponent exceeds the kernel
base, satisfies the complete second-observer tailF package (dodges every
gate: sheet, second-sheet, row, tower), and lies in one of the 32
surviving level-five residue classes.  This is the intersection of the
tailF residual with the level-five survivor tree — the smallest family
the campaign has ever reduced the full statement to. -/
def CombinedResidual (K : Nat) : Prop :=
  500 < K ∧ GSTGraphV2OmegaWaveLaw.omegaShadowTailF K ∧
    GSTShadowSeparationAttack.survivor5 (K % 243) = true

/-- **THE CROWN, EQUIVALENT TO THE COMBINED RESIDUAL.**  The full
unconditional statement — every `n ≥ 9` has `noTernaryTwo (2 ^ n) =
false` — holds if and only if every combined-residual exponent owns a
ternary digit two.  Everything else in the entire campaign folds into
the two directions of this one equivalence: the odd wing, the kernel
base, the non-shadow kills, the five gates, and the 211 killed
level-five classes. -/
theorem erdos_ternary_2_iff_combined_residual :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2 ^ n) = false) ↔
      (∀ K : Nat, CombinedResidual K → ∃ p : Nat, (4 ^ K) / 3 ^ p % 3 = 2) := by
  constructor
  · intro hCrown K hK
    obtain ⟨h500, _, _⟩ := hK
    have hn18 : 9 ≤ 2 * K := by omega
    have h2n : noTernaryTwo (2 ^ (2 * K)) = false := hCrown (2 * K) hn18
    have h4eq : 2 ^ (2 * K) = 4 ^ K := by
      rw [show (4 : Nat) = 2 ^ 2 from by decide, Nat.pow_mul]
    rw [h4eq] at h2n
    obtain ⟨p, hp⟩ := no_two_false_digit_witness (4 ^ K) h2n
    exact ⟨p, hp⟩
  · intro hRes n hn
    by_cases hodd : n % 2 = 1
    · exact erdos_ternary_2_odd_universal n hn hodd
    · have h4eq : 2 ^ n = 4 ^ (n / 2) := by
        have hn_eq : n = 2 * (n / 2) := by omega
        rw [show (4 : Nat) = 2 ^ 2 from by decide, ← Nat.pow_mul, ← hn_eq]
      rw [h4eq]
      refine has_two_imp_not_no_two (4 ^ (n / 2)) ?_
      by_cases h500 : n / 2 ≤ 500
      · exact modular_check_base (n / 2) (by omega) h500
      · have hK8 : 8 ≤ n / 2 := by omega
        rcases GSTGraphV2OmegaWaveLaw.omega_digit_two_cases (n / 2) hK8 with
          hShadow | ⟨p, hp⟩
        · rcases shadow_split_of_gates (n / 2) hK8 hShadow with hT | ⟨p, hp⟩
          · by_cases hs5 : GSTShadowSeparationAttack.survivor5 (n / 2 % 243) = true
            · obtain ⟨p, hp⟩ := hRes (n / 2) ⟨by omega, hT, hs5⟩
              exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
            · have hkill : GSTShadowSeparationAttack.survivor5 (n / 2 % 243) = false := by
                cases hh : GSTShadowSeparationAttack.survivor5 (n / 2 % 243) with
                | true => exact absurd hh hs5
                | false => rfl
              obtain ⟨p, _, hp⟩ :=
                GSTShadowSeparationAttack.separation_level_five (n / 2) hkill
              exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
          · exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp
        · exact hasTernaryTwo_of_digit (4 ^ (n / 2)) p hp

/-! ## The eternal shadows live in the residual -/

/-- Every eternal shadow from five on is a combined-residual exponent:
an exponent with no ternary digit two anywhere must exceed the kernel
base (the base would fire it), dodge every gate of the five-gate
dispatch (each gate fires a digit two), and sit in a level-five
surviving class (the killed classes fire below row six). -/
theorem eternally_shadowed_combined (m : Nat) (hm : 5 ≤ m)
    (hE : GSTShadowGapReceipt.EternallyShadowed m) :
    CombinedResidual m := by
  have hbase : 500 < m := by
    by_contra h500
    have hle : m ≤ 500 := by omega
    obtain ⟨q, hq, _⟩ :=
      hasTernaryTwo_first_pos (4 ^ m) (modular_check_base m hm hle)
    exact hE q q (Nat.lt_succ_self q) hq
  refine ⟨hbase, ?_, ?_⟩
  · have hK8 : 8 ≤ m := by omega
    rcases GSTGraphV2OmegaWaveLaw.omega_digit_two_cases m hK8 with
      hShadow | ⟨p, hp⟩
    · rcases shadow_split_of_gates m hK8 hShadow with hT | ⟨p, hp⟩
      · exact hT
      · exact absurd hp (hE p p (Nat.lt_succ_self p))
    · exact absurd hp (hE p p (Nat.lt_succ_self p))
  · rcases GSTShadowSeparationAttack.level_five_reach m with hs | ⟨p, _, hp⟩
    · exact hs
    · exact absurd hp (hE p p (Nat.lt_succ_self p))

/-- **THE RESIDUAL-FIRING STATEMENT IS A SEPARATION SUPPLIER.**  If
every combined-residual exponent owns a ternary digit two, then no
exponent from five on is eternally shadowed — the door-ten statement.
Combined with the shadow-gap receipt's equivalence, the residual family
is the war: kill it and the full unconditional crown follows. -/
theorem separation_of_residual_firing
    (h : ∀ K : Nat, CombinedResidual K → ∃ p : Nat, (4 ^ K) / 3 ^ p % 3 = 2) :
    ∀ m : Nat, 5 ≤ m → ¬ GSTShadowGapReceipt.EternallyShadowed m := by
  intro m hm hE
  obtain ⟨p, hp⟩ := h m (eternally_shadowed_combined m hm hE)
  exact hE p p (Nat.lt_succ_self p) hp

/-! ## Receipts -/

#print axioms shadow_split_of_gates
#print axioms erdos_ternary_2_unconditional_coverage
#print axioms erdos_ternary_2_iff_combined_residual
#print axioms eternally_shadowed_combined
#print axioms separation_of_residual_firing

#check @shadow_split_of_gates
#check @erdos_ternary_2_unconditional_coverage
#check @erdos_ternary_2_iff_combined_residual
#check @CombinedResidual
#check @eternally_shadowed_combined
#check @separation_of_residual_firing

end GSTUnconditionalCoverage
