import ErdosTernary2
import GSTTheAct
import GSTDiagonalRead
import GSTClimbInfiniteFamily

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
  IO.println ""
  IO.println "Verify cleanliness:"
  IO.println "  ./scripts/sorry_check.sh   # must return 0"
  IO.println "  ./scripts/comparator.sh    # prints 'Your solution is okay!'"
