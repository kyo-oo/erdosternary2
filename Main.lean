import ErdosTernary2
import GSTTheAct
import GSTDiagonalRead
import GSTClimbInfiniteFamily
import GSTTheActConstruction

/-!
# ErdosTernary2 — the monolith's entry face

The monolith now carries the campaign's closure state, wired in at its
own entry point by explicit order:

* `the_monolith_wire` — the assembled faces: (1) THE TOWER DUST IS EMPTY
  (no three-free core has a never-firing multiplicative-three tower —
  `GSTClimbInfiniteFamily.tower_dust_empty`); (2) the standing collapse
  (the act ⟺ no Cantorian exponent from eight on); (3) the final socket
  (no Cantorian exponent from eight on ⇒ `hTailF`); (4) the identity
  (`hTailF` ⟺ the even-exponent statement itself).

* `the_construction_wire` — THE FEEDBACK READ, wired at the same face:
  the act as the feedback tree's escape (`the_act_iff_feedback`), carried
  through the construction module (`GSTTheActConstruction`).  The
  construction's own face: every row of every power reads the exponent
  through the prefix-power (`self_read`), the uniform kill engine
  (`feedback_fire_of_class`), cascade level four (eight classes fire at
  row five), and the survivor map (sixteen nodes mod 243).
-/

/-- **THE MONOLITH WIRE.**  The campaign's closure state, carried at the
monolith's own entry face: the never-firing towers are all dead, the act
is exactly the absence of Cantorian exponents from eight on, the socket
from that absence to `hTailF` stands green, and `hTailF` is the
even-exponent statement itself. -/
theorem the_monolith_wire :
    (∀ core : Nat, ¬ 3 ∣ core →
      ¬ GSTClimbInfiniteFamily.NeverFiringTower core) ∧
    (GSTTheAct.the_act ↔ ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K) ∧
    (∀ h : ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K,
      GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false) :=
  ⟨GSTClimbInfiniteFamily.tower_dust_empty,
    GSTClimbInfiniteFamily.the_act_iff_no_cantorian,
    GSTClimbInfiniteFamily.hTailF_of_no_cantorian,
    GSTTailFProof.hTailF_iff_even_conjecture⟩

#print axioms the_monolith_wire

/-- **THE CONSTRUCTION WIRE.**  The feedback read, carried at the
monolith's own entry face: the act holds IF AND ONLY IF every exponent
from eight on fires somewhere in the feedback tree — some level `j`
where the prefix noise plus the exponent's own `j`-th trit lands on
two.  Through the construction module and the standing green identity,
the tree-escape and `hTailF` are one object. -/
theorem the_construction_wire :
    (∀ K : Nat, 8 ≤ K → ∃ j : Nat,
      (GSTCanonicalSevenAxisBridge.digit3 (4^(K % 3^j)) (j + 1)
        + GSTCanonicalSevenAxisBridge.digit3 K j) % 3 = 2) ↔
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  (GSTTheActConstruction.the_act_iff_feedback).symm.trans
    GSTTheAct.the_act_iff_hTailF

#print axioms the_construction_wire

/-- Entry point: prints workspace status and points to the comparator. -/
def main : IO Unit := do
  IO.println "ErdosTernary2 — Lean formalization workspace"
  IO.println "================================================"
  IO.println "Toolchain: leanprover/lean4 (see lean-toolchain)"
  IO.println ""
  IO.println "Proven theorems (0 sorries, 0 errors):"
  IO.println "  - ErdosTernary2.lt_three_cases"
  IO.println "  - ErdosTernary2.ternary_digit_lt_three"
  IO.println "  - ErdosTernary2.empty_foldr_repr_zero"
  IO.println "  - ErdosTernary2.single_digit_value"
  IO.println "  - ErdosTernary2.two_digit_value"
  IO.println "  - ErdosTernary2.isTernaryDigit_{zero,one,two,three}"
  IO.println ""
  IO.println "Campaign closure state (wired at the monolith face):"
  IO.println "  - the_monolith_wire: tower dust empty; the act <=> no"
  IO.println "    Cantorian exponent from 8 on; socket to hTailF green."
  IO.println "  - the_construction_wire: the act <=> the feedback tree's"
  IO.println "    escape (self_read + uniform kill engine + level-four map)."
  IO.println ""
  IO.println "Verify cleanliness:"
  IO.println "  ./scripts/sorry_check.sh   # must return 0"
  IO.println "  ./scripts/comparator.sh    # prints 'Your solution is okay!'"
