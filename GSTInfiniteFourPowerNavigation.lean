import GSTGraphV2PerfectPowerBlockCollision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteFourPowerNavigation

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2PerfectPowerBlockCollision
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope

/-- A Happy gate three horizontal x4 steps later cannot disappear at every
vertical coordinate above the fixed cut `3`.  This is the universal width-3
perfect-power collision, independent of the prefix-one branch. -/
theorem power_three_step_collision
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (3+j)).seven.carry
      (graph (4^K) 3 (3+j)).seven.digit) :
    False := by
  let E := 4^K
  let N : Nat := 3
  let b : Nat := 3

  have hleft :
      0 < graphPhaseWindow E 0 b (q+1) := by
    apply graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hright :
      graphPhaseWindow E N b (q+1) ≤ 0 := by
    apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hleftAbs : HappyCell
      (graph 1 K (b+q)).seven.carry
      (graph 1 K (b+q)).seven.digit := by
    have hiff := power_origin_happy_iff K 0 (b+q)
    exact hiff.mp (by simpa [E, b, Nat.add_assoc] using hChild)

  have hrightAbs : ∀ j, ¬ HappyCell
      (graph 1 (K+N) (b+j)).seven.carry
      (graph 1 (K+N) (b+j)).seven.digit := by
    intro j h
    apply hRightBad j
    have hiff := power_origin_happy_iff K N (b+j)
    exact hiff.mpr (by simpa [E, N] using h)

  have hU := unified_equationIII_vertical_telescope E N b (q+1)
  have hPureRight := blockDensity_prefix_nonpositive_of_bad E N b (q+1)
    (fun j hj => by simpa [E, N, b, Nat.add_assoc] using hRightBad j)
  have hPureExact := blockDensity_column_exact E N b (q+1)

  dsimp [E, N, b] at hleft hright hleftAbs hrightAbs hU hPureRight hPureExact ⊢
  omega

/-- From exponent 8 onward a Happy gate exists at a ternary coordinate at
least 3.  The induction advances by exactly three horizontal x4 steps. -/
theorem four_power_happy_ge_three (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^k) p) (digit3 (4^k) p) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hk11 : 11 ≤ k
      · have hk3 : 8 ≤ k - 3 := by omega
        obtain ⟨p, hp3, hpHappy⟩ := ih (k - 3) (by omega) hk3
        let q := p - 3
        have hpq : 3 + q = p := by
          dsimp [q]
          omega
        have hChild : HappyCell
            (graph (4^(k-3)) 0 (3+q)).seven.carry
            (graph (4^(k-3)) 0 (3+q)).seven.digit := by
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hpq] using hpHappy
        by_contra hno
        have hRightBad : ∀ j, ¬ HappyCell
            (graph (4^(k-3)) 3 (3+j)).seven.carry
            (graph (4^(k-3)) 3 (3+j)).seven.digit := by
          intro j hright
          apply hno
          refine ⟨3+j, by omega, ?_⟩
          have hpow : 4^3 * 4^(k-3) = 4^k := by
            rw [← Nat.pow_add]
            congr 1
            omega
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hpow] using hright
        exact power_three_step_collision (k-3) q hChild hRightBad
      · have hkCases : k = 8 ∨ k = 9 ∨ k = 10 := by omega
        rcases hkCases with rfl | rfl | rfl
        · refine ⟨4, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨7, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨10, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]

/-- A Happy cell is already the first branch of the historical creation
certificate: its carry is 0 or 3, hence zero modulo three. -/
theorem happy_to_creation_certificate
    (R p : Nat) (hp : 1 ≤ p)
    (hHappy : HappyCell (carry4 R p) (digit3 R p)) :
    R / 3^p % 3 = 2 ∧
      ((4 * (R % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * (R % 3^p)) / 3^p % 3 = 1 ∧
        R / 3^(p+1) % 3 = 2)) := by
  rcases hHappy with ⟨hd, hC⟩
  constructor
  · simpa [digit3] using hd
  · left
    rcases hC with h0 | h3
    · simpa [carry4, h0]
    · simpa [carry4, h3]

/-- Universal replacement for the broken recursive `h_creation_for_4pow`.
The public contract is exactly the historical `(k,hk5,hk7)` API. -/
theorem gst_four_power_navigation_universal
    (k : Nat) (hk5 : 5 ≤ k) (hk7 : k ≠ 7) :
    ∃ p : Nat, 1 ≤ p ∧ (4^k) / 3^p % 3 = 2 ∧
      ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧
        (4^k) / 3^(p+1) % 3 = 2)) := by
  by_cases hk8 : 8 ≤ k
  · obtain ⟨p, hp3, hHappy⟩ := four_power_happy_ge_three k hk8
    obtain ⟨hd, hc⟩ := happy_to_creation_certificate (4^k) p (by omega) hHappy
    exact ⟨p, by omega, hd, hc⟩
  · have hkCases : k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hkCases with rfl | rfl | rfl
    · refine ⟨2, by decide, ?_⟩
      norm_num
    · refine ⟨2, by decide, ?_⟩
      norm_num
    · exact (hk7 rfl).elim

#print axioms power_three_step_collision
#print axioms four_power_happy_ge_three
#print axioms gst_four_power_navigation_universal

-- diagnostic push marker
end GSTInfiniteFourPowerNavigation
