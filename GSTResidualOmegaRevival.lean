import ErdosTernary2
import GSTFinalPrefixOneDirectU2DCollision
import GSTFinalResidualConnector
import GSTTheAct

namespace GSTResidualOmegaRevival

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open GSTCanonicalTailStateIso
open GSTFinalPrefixOneDirectU2DCollision

/-- Convert the monolith Navigation wrapper to the standalone physical
Happy-cell Navigation used by the direct U2D collision theorem. -/
theorem standalone_navigation_of_navigation_witness
    (R : Nat) (h : GSTNavigationWitness R) :
    GSTCanonicalTailStateIso.Navigation R := by
  obtain ⟨j, hd, hspace⟩ := h
  have hmod : gstCarry R j % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero R j hspace
  have hlt : gstCarry R j < 4 := by
    cases j with
    | zero =>
        simp [gstCarry, Nat.mod_one]
    | succ q =>
        exact gstCarry_lt_four R (q+1) (by omega)
  have hcarry : gstCarry R j = 0 ∨ gstCarry R j = 3 := by
    omega
  refine ⟨j, ?_⟩
  constructor
  · simpa [GSTCanonicalTailStateIso.digit3, gstDigit] using hd
  · rcases hcarry with h0 | h3
    · exact Or.inl (by
        simpa [GSTCanonicalTailStateIso.carry4, gstCarry] using h0)
    · exact Or.inr (by
        simpa [GSTCanonicalTailStateIso.carry4, gstCarry] using h3)

/-- The one genuinely necessary residual constructor.  A hypothetical
prefix-one parent failure is an all-depth Omega bad trace.  The existing
residual connector reads it as an all-bad right boundary, while the child
Navigation witness is a Happy left gate.  The direct U2D crossing theorem
proves that these two boundary conditions cannot coexist. -/
theorem prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hno
  have hbad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hno
  have hRightBad :=
    GSTFinalResidualConnector.residual_bad_trace_to_right_bad
      s 1 n hs (by decide) hbad
  have hstand :
      GSTCanonicalTailStateIso.Navigation
        (GSTFinalPrefixOneDirectU2DCollision.directChild s n) := by
    change GSTCanonicalTailStateIso.Navigation
      (gstNavigationConstant (s+1) n)
    exact standalone_navigation_of_navigation_witness
      (gstNavigationConstant (s+1) n) hchild
  exact GSTFinalPrefixOneDirectU2DCollision.canonical_perfect_power_block_collision_direct
    s n hs hn hstand (by
      intro j
      simpa [Nat.add_assoc] using hRightBad j)

/-- The monolith already proves that one-place prefix-one lifting generates
all residual wave depths by peeling powers of three from the origin. -/
theorem residual_navigation_lift : GSTResidualNavigationLift :=
  gst_residual_navigation_lift_of_prefix_one prefix_one_navigation_lift

/-- Universal canonical Navigation, now with no custom premise. -/
theorem navigation_all :
    ∀ s b, 1 ≤ s → 1 ≤ b → b % 3 ≠ 0 → (2 ≤ s ∨ 1 < b) →
      GSTNavigationWitness (gstNavigationConstant s b) :=
  gst_navigation_witness_all_of_prefix_one prefix_one_navigation_lift

/-- Every sufficiently large exponent divisible by three has a physical
Navigation witness in its full power of four. -/
theorem four_power_navigation_div_three
    (K : Nat) (hK : 500 < K) (hK3 : K % 3 = 0) :
    GSTNavigationWitness (4^K) :=
  gst_navigation_witness_four_pow_div_three_of_prefix_one
    prefix_one_navigation_lift K hK hK3

/-- Binder-free universal even-power theorem.  The finite kernel handles
K <= 500; class two fires directly; class zero uses universal Navigation;
class one lifts the Navigation gate from K-1 through multiplication by four. -/
theorem even_universal (K : Nat) (hK : 5 ≤ K) :
    hasTernaryTwo (4^K) = true := by
  by_cases h500 : K ≤ 500
  · exact modular_check_base K hK h500
  · have hmodlt : K % 3 < 3 := Nat.mod_lt _ (by decide)
    by_cases h2 : K % 3 = 2
    · exact even_case_a_mod3_2 K h2
    · by_cases h0 : K % 3 = 0
      · obtain ⟨p, hd, _hspace⟩ :=
          four_power_navigation_div_three K (by omega) h0
        exact hasTernaryTwo_of_digit (4^K) p hd
      · have h1 : K % 3 = 1 := by omega
        have hKm1 : 500 < K - 1 := by omega
        have hKm1mod : (K - 1) % 3 = 0 := by omega
        obtain ⟨p, hd, hspace⟩ :=
          four_power_navigation_div_three (K-1) hKm1 hKm1mod
        have hp : 1 ≤ p := by
          cases p with
          | zero =>
              simp only [gstDigit, Nat.pow_zero, Nat.div_one] at hd
              have hmod : 4^(K-1) % 3 = 1 := by
                rw [Nat.pow_mod]
                simp
              omega
          | succ q => omega
        have hCmod : gstCarry (4^(K-1)) p % 3 = 0 :=
          gstGoodSpace_carry_mod3_zero (4^(K-1)) p hspace
        have hClt : gstCarry (4^(K-1)) p < 4 :=
          gstCarry_lt_four (4^(K-1)) p hp
        have hgood : gstCarry (4^(K-1)) p = 0 ∨
            gstCarry (4^(K-1)) p = 3 := by
          omega
        have hlift :=
          gst_pure_lift_or_forced_cascade (4^(K-1)) p hp hd hgood
        have hd4 : gstDigit (4 * 4^(K-1)) p = 2 := by
          rcases hlift with h | h
          · exact h.1
          · exact h.1
        have hpow : 4 * 4^(K-1) = 4^K := by
          have hKeq : K = (K-1) + 1 := by omega
          calc
            4 * 4^(K-1) = 4^(K-1) * 4 := by ac_rfl
            _ = 4^((K-1)+1) := (Nat.pow_succ 4 (K-1)).symm
            _ = 4^K := by rw [← hKeq]
        rw [hpow] at hd4
        exact hasTernaryTwo_of_digit (4^K) p hd4

/-- Binder-free THE ACT. -/
theorem the_act : GSTTheAct.the_act := by
  intro K hK
  exact has_two_imp_not_no_two (4^K) (even_universal K (by omega))

/-- Binder-free full Erdős ternary-two statement. -/
theorem full_erdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  GSTTheAct.full_erdos_of_the_act the_act

#print axioms standalone_navigation_of_navigation_witness
#print axioms prefix_one_navigation_lift
#print axioms residual_navigation_lift
#print axioms navigation_all
#print axioms four_power_navigation_div_three
#print axioms even_universal
#print axioms the_act
#print axioms full_erdos

end GSTResidualOmegaRevival
