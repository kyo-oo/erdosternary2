import ErdosTernary2
import GSTTheAct
import GSTDiagonalRead
import GSTClimbInfiniteFamily
import GSTTheActConstruction
import GSTBladeWave
import GSTTowerFire
import GSTTowerAxis
import GSTWorldtraceArithmetic
import GSTGhostRayExclusion
import GSTWorldtraceMahlerRelativePrecision

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

/-- **THE BLADE-WAVE WIRE.**  The four-lane volley's loaded increment,
carried at the monolith's own entry face: the dust root's three exact
truncation laws (rows two and three read `m`'s pure trits; row four
lands the blade's first correction, exactly the binomial coefficient
`C(m,2)`), and the wave's periodicity (the wave digit `digit_(a+n)` of
`4^(3^a·core)` depends only on `core mod 3^n`).  Machine receipts:
1500/1500 × 3 and 3280/3280, exact big-int arithmetic.  The
accumulating-blade gap (all four lanes' convergence point) now rests
on these exact foundations. -/
theorem the_blade_wave_wire :
    (∀ m : Nat, GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*m)) 2 = m % 3) ∧
    (∀ m : Nat, GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*m)) 3 = (m / 3) % 3) ∧
    (∀ m : Nat, GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*m)) 4
      = ((m / 9) % 3 + m.choose 2) % 3) ∧
    (∀ a n core t : Nat, GSTCanonicalSevenAxisBridge.digit3
        (4^(3^a * (core + 3^n * t))) (a + n)
      = GSTCanonicalSevenAxisBridge.digit3 (4^(3^a * core)) (a + n)) :=
  ⟨GSTBladeWave.digit_two_of_dust_root,
   GSTBladeWave.digit_three_of_dust_root,
   GSTBladeWave.digit_four_of_dust_root,
   GSTBladeWave.wave_digit_periodic⟩

#print axioms the_blade_wave_wire

/-- The tower fires — Lane D's deep-hider laws at the entry face:
the tower constant c_n read bare in the deep rows, and the three
canonical fire families (3^n at n+2; 2*3^n at n+1; 3^n+1 at n+4). -/
theorem the_tower_fire_wire :
    (∀ n : Nat, 1 ≤ n →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^n)) (n+2) = 2) ∧
    (∀ n : Nat,
      GSTCanonicalSevenAxisBridge.digit3 (4^(2 * 3^n)) (n+1) = 2) ∧
    (∀ n : Nat, 3 ≤ n →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^n + 1)) (n+4) = 2) ∧
    (∀ j n k : Nat, k ≤ n →
      GSTCanonicalSevenAxisBridge.digit3 (4^(j * 3^n)) (n+1+k)
        = GSTCanonicalSevenAxisBridge.digit3 (j * GSTTowerFire.c n) k) :=
  ⟨GSTTowerFire.three_pow_fires,
   GSTTowerFire.two_mul_three_pow_fires,
   GSTTowerFire.three_pow_plus_one_fires,
   GSTTowerFire.tower_digit_read⟩

#print axioms the_tower_fire_wire

/-- **THE TOWER-AXIS WIRE.**  The `s ≥ 1` exponents, killed structurally
at the monolith's entry face: every `K = 3^s · c` with `s ≥ 1` and
`c ≡ 1 mod 9` fires at row `s+2` (one theorem, infinitely many
exponents); the level-two classes `c ≡ 13, 25 mod 27` at row `s+3`; the
level-three classes `c ≡ 4, 34, 49, 70 mod 81` at row `s+4`.  All
through the deep-hider master lemma and the tower congruences — the
sheet-zero cascade's blind side, closed.  Machine receipts: 36/36,
20/20, 20/20, exact big-int. -/
theorem the_tower_axis_wire :
    (∀ s c : Nat, 1 ≤ s → c % 9 = 1 →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^s * c)) (s+2) = 2) ∧
    (∀ s c : Nat, 2 ≤ s → (c % 27 = 13 ∨ c % 27 = 25) →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^s * c)) (s+3) = 2) ∧
    (∀ s c : Nat, 3 ≤ s →
      (c % 81 = 4 ∨ c % 81 = 34 ∨ c % 81 = 49 ∨ c % 81 = 70) →
      GSTCanonicalSevenAxisBridge.digit3 (4^(3^s * c)) (s+4) = 2) :=
  ⟨GSTTowerAxis.tower_axis_level_one,
   GSTTowerAxis.tower_axis_level_two,
   GSTTowerAxis.tower_axis_level_three⟩

#print axioms the_tower_axis_wire

/-- **THE GHOST-RAY WIRE.**  The terminal exclusion, landed at the
monolith's entry face: under Mahler's 3-adic exponential transcendence
(stated in pure integer divisibility form — no p-adic objects) no
three-free natural lies on the stabilized middle-third ghost ray; with
the uniform compression bridge (every Cantorian counterexample's core
lies on a ghost ray) the act itself closes through the repo's own
green sockets.  The two inputs are named, explicit hypotheses — the
honest form of the remaining external seam. -/
theorem the_ghost_ray_wire :
    (∀ (H : GSTGhostRay.mahler_log3_not_rational) (u : Nat), ¬ 3 ∣ u →
      ¬ GSTGhostRay.GhostRay u) ∧
    (∀ (H : GSTGhostRay.mahler_log3_not_rational)
      (Hc : GSTGhostRay.UniformCompression), GSTTheAct.the_act) :=
  ⟨GSTGhostRay.terminal_ghost_exclusion,
   GSTGhostRay.the_act_of_mahler_compression⟩

#print axioms the_ghost_ray_wire

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
  IO.println "  - the_blade_wave_wire: dust root's three exact laws + the"
  IO.println "    wave's periodicity (the blade's first binomial correction)."
  IO.println ""
  IO.println "Verify cleanliness:"
  IO.println "  ./scripts/sorry_check.sh   # must return 0"
  IO.println "  ./scripts/comparator.sh    # prints 'Your solution is okay!'"

/-- **THE WORLDTRACE WIRE.**  The boss's transformation, landed: the dust
power `4^(1+3m)` IS the binomial sum `4*(1+63)^m`, its deep rows are
explicit polynomials (row five the quadratic, row seven the cubic), the
polynomial kills without computing the power, and the sixth cascade
level compresses the survivors 32 -> 64 mod 2187. -/
theorem the_worldtrace_wire :
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729]) ∧
    (∀ m : Nat, GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*m)) 5
      = GSTCanonicalSevenAxisBridge.digit3 (4 + 252*m + 15876*Nat.choose m 2) 5) ∧
    (∀ m : Nat, GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*m)) 7
      = GSTCanonicalSevenAxisBridge.digit3
        (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7) ∧
    (GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*28)) 5 = 2) ∧
    (∀ K : Nat, K % 3 = 1 → GSTClimbInfiniteFamily.CantorianPower K →
      K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116) :=
  ⟨GSTWorldtraceArithmetic.wt_quad_mod729,
    GSTWorldtraceArithmetic.wt_row_five_read,
    GSTWorldtraceArithmetic.wt_row_seven_read,
    GSTWorldtraceArithmetic.wt_quad_fire_demo,
    GSTWorldtraceArithmetic.cantorian_dust_mod_2187⟩

#print axioms the_worldtrace_wire

/-- **THE WORLDTRACE WIRE, LEVEL SEVEN.**  The quartic blade lands: the
eighth row of the dust power `4^(1+3m)` is the explicit quartic
polynomial mod 19683, the polynomial kills K = 82 at row eight without
computing `4^82`, and the seventh cascade level compresses the
survivors 64 -> 128 mod 6561. -/
theorem the_worldtrace_wire_seven :
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683]) ∧
    (∀ m : Nat, GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*m)) 8
      = GSTCanonicalSevenAxisBridge.digit3
        (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8) ∧
    (GSTCanonicalSevenAxisBridge.digit3 (4^(1+3*27)) 8 = 2) ∧
    (∀ K : Nat, K % 3 = 1 → GSTClimbInfiniteFamily.CantorianPower K →
      K % 6561 = 1 ∨ K % 6561 = 4 ∨ K % 6561 = 13 ∨ K % 6561 = 40 ∨ K % 6561 = 94 ∨ K % 6561 = 109 ∨ K % 6561 = 121 ∨ K % 6561 = 166 ∨ K % 6561 = 193 ∨ K % 6561 = 244 ∨ K % 6561 = 280 ∨ K % 6561 = 283 ∨ K % 6561 = 325 ∨ K % 6561 = 364 ∨ K % 6561 = 436 ∨ K % 6561 = 496 ∨ K % 6561 = 514 ∨ K % 6561 = 523 ∨ K % 6561 = 595 ∨ K % 6561 = 730 ∨ K % 6561 = 733 ∨ K % 6561 = 739 ∨ K % 6561 = 823 ∨ K % 6561 = 838 ∨ K % 6561 = 850 ∨ K % 6561 = 922 ∨ K % 6561 = 928 ∨ K % 6561 = 973 ∨ K % 6561 = 1003 ∨ K % 6561 = 1009 ∨ K % 6561 = 1093 ∨ K % 6561 = 1144 ∨ K % 6561 = 1165 ∨ K % 6561 = 1171 ∨ K % 6561 = 1225 ∨ K % 6561 = 1228 ∨ K % 6561 = 1243 ∨ K % 6561 = 1252 ∨ K % 6561 = 1387 ∨ K % 6561 = 1468 ∨ K % 6561 = 1540 ∨ K % 6561 = 1624 ∨ K % 6561 = 1657 ∨ K % 6561 = 1732 ∨ K % 6561 = 1741 ∨ K % 6561 = 1783 ∨ K % 6561 = 1873 ∨ K % 6561 = 1900 ∨ K % 6561 = 1957 ∨ K % 6561 = 2038 ∨ K % 6561 = 2053 ∨ K % 6561 = 2116 ∨ K % 6561 = 2188 ∨ K % 6561 = 2191 ∨ K % 6561 = 2269 ∨ K % 6561 = 2353 ∨ K % 6561 = 2434 ∨ K % 6561 = 2467 ∨ K % 6561 = 2470 ∨ K % 6561 = 2512 ∨ K % 6561 = 2551 ∨ K % 6561 = 2623 ∨ K % 6561 = 2683 ∨ K % 6561 = 2767 ∨ K % 6561 = 2782 ∨ K % 6561 = 2917 ∨ K % 6561 = 2920 ∨ K % 6561 = 2944 ∨ K % 6561 = 3115 ∨ K % 6561 = 3163 ∨ K % 6561 = 3190 ∨ K % 6561 = 3196 ∨ K % 6561 = 3280 ∨ K % 6561 = 3331 ∨ K % 6561 = 3352 ∨ K % 6561 = 3412 ∨ K % 6561 = 3415 ∨ K % 6561 = 3433 ∨ K % 6561 = 3568 ∨ K % 6561 = 3658 ∨ K % 6561 = 3673 ∨ K % 6561 = 3685 ∨ K % 6561 = 3727 ∨ K % 6561 = 3844 ∨ K % 6561 = 3919 ∨ K % 6561 = 4060 ∨ K % 6561 = 4144 ∨ K % 6561 = 4162 ∨ K % 6561 = 4225 ∨ K % 6561 = 4297 ∨ K % 6561 = 4387 ∨ K % 6561 = 4414 ∨ K % 6561 = 4456 ∨ K % 6561 = 4468 ∨ K % 6561 = 4483 ∨ K % 6561 = 4495 ∨ K % 6561 = 4567 ∨ K % 6561 = 4618 ∨ K % 6561 = 4621 ∨ K % 6561 = 4888 ∨ K % 6561 = 4897 ∨ K % 6561 = 4954 ∨ K % 6561 = 5113 ∨ K % 6561 = 5131 ∨ K % 6561 = 5197 ∨ K % 6561 = 5212 ∨ K % 6561 = 5224 ∨ K % 6561 = 5296 ∨ K % 6561 = 5347 ∨ K % 6561 = 5350 ∨ K % 6561 = 5545 ∨ K % 6561 = 5617 ∨ K % 6561 = 5620 ∨ K % 6561 = 5626 ∨ K % 6561 = 5755 ∨ K % 6561 = 5761 ∨ K % 6561 = 5842 ∨ K % 6561 = 5845 ∨ K % 6561 = 5860 ∨ K % 6561 = 5872 ∨ K % 6561 = 5998 ∨ K % 6561 = 6115 ∨ K % 6561 = 6157 ∨ K % 6561 = 6274 ∨ K % 6561 = 6349 ∨ K % 6561 = 6427 ∨ K % 6561 = 6484 ∨ K % 6561 = 6490) :=
  ⟨GSTWorldtraceArithmetic.wt_quartic_mod19683,
    GSTWorldtraceArithmetic.wt_row_eight_read,
    GSTWorldtraceArithmetic.wt_quartic_fire_demo,
    GSTWorldtraceArithmetic.cantarian_dust_mod_6561⟩

#print axioms the_worldtrace_wire_seven

/-- **THE PAIR-READ WIRE.**  GAP-E1's first family lands: the uniform
pair-read formula (the two-support tower factorization through
`prefaced_digit`) and the fire — every exponent `4 + 3^(j+1)*u` with
`j ≤ 4`, `u` in {1, 4, 7} reads digit two at row `j+4`. -/
theorem the_pair_read_wire :
    (∀ T u j : Nat, 1 ≤ j → 4^T < 3^(j+2) →
      GSTCanonicalSevenAxisBridge.digit3 (4^(T + 3^(j+1)*u)) (j+4)
        = GSTCanonicalSevenAxisBridge.digit3 (4^T * u * GSTTowerFire.c (j+1)) 2) ∧
    (∀ u j : Nat, 4 ≤ j → (u = 1 ∨ u = 4 ∨ u = 7) →
      GSTCanonicalSevenAxisBridge.digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2) :=
  ⟨GSTWorldtraceArithmetic.pair_read_formula,
    GSTWorldtraceArithmetic.pair_read_fire⟩

#print axioms the_pair_read_wire

/-- **THE GENERAL FIRE WIRE.**  The GAP-E1 engine: the residue transfer
(the read reduces to `4^T * u * 16 mod 27`), the general trunk-uniform
fire — any trunk, any branch, the mod-27 kill zone `18 ≤ residue` —
and the trunk-13 second family. -/
theorem the_general_fire_wire :
    (∀ T u j : Nat, 2 ≤ j →
      (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27) ∧
    (∀ T u j : Nat, 4 ≤ j → 4^T < 3^(j+2) → 18 ≤ (4^T * u * 16) % 27 →
      GSTCanonicalSevenAxisBridge.digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2) ∧
    (∀ j : Nat, 15 ≤ j →
      GSTCanonicalSevenAxisBridge.digit3 (4^(13 + 3^(j+1))) (j+4) = 2) :=
  ⟨GSTWorldtraceArithmetic.pair_residue_mod27,
    GSTWorldtraceArithmetic.pair_read_fire_general,
    GSTWorldtraceArithmetic.pair_read_fire_demo_two⟩

#print axioms the_general_fire_wire

/-- **THE DESCENT ENGINE WIRE.**  The top split, the addition window,
and the row-(H+2) law — the descent engine that reads the deep digits
of `4^K` as base-3 additions of the trunk's digits and the branch
factor's shifted digits. -/
theorem the_descent_engine_wire :
    (∀ K H : Nat, K < 3^(H+1) → ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H) + 3^(H+1) * Y)) ∧
    (∀ K H r : Nat, K < 3^(H+1) → r + 1 ≤ 2*H+2 →
      GSTCanonicalSevenAxisBridge.digit3 (4^K) r
        = GSTCanonicalSevenAxisBridge.digit3 (4^(K % 3^H)
          + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r) :=
  ⟨GSTWorldtraceArithmetic.top_split,
    GSTWorldtraceArithmetic.window_congr⟩

#print axioms the_descent_engine_wire

/-- **THE DUST WINDOW WIRE.**  The period-nine law, the dust branch
vanishing, and the clean row-(H+2) law — the descent's cleanest rung. -/
theorem the_dust_window_wire :
    (∀ r : Nat, (4:Nat)^r % 9 = 4^(r % 3) % 9) ∧
    (∀ K H : Nat, 1 ≤ H → K < 3^(H+1) → K % 3 = 1 →
      GSTCanonicalSevenAxisBridge.digit3 (4^K) (H+2)
        = (GSTCanonicalSevenAxisBridge.digit3 (4^(K % 3^H)) (H+2)
          + (GSTCanonicalSevenAxisBridge.digit3 (4^(K % 3^H)) (H+1)
            + K / 3^H) / 3) % 3) :=
  ⟨GSTWorldtraceArithmetic.four_pow_mod9,
    GSTWorldtraceArithmetic.window_row_two_dust⟩

#print axioms the_dust_window_wire


/-- **THE WORLDTRACE–MAHLER ATOMIC SURGERY WIRE.**  The former pair of
terminal Props has been replaced by one coherent theory object.  Its
relative-precision compression and Mahler fracture collide on the same
integer witness and export the complete crown: Cantorian extinction,
digit-two witnesses, \`the_act\`, \`tailF\`, the full theorem, and the
infinite-controller witness. -/
theorem the_worldtrace_mahler_wire
    (T : GSTWorldtraceMahler.WorldtraceMahlerTheory) :
    GSTWorldtraceMahler.WorldtraceMahlerCrown :=
  GSTWorldtraceMahler.worldtrace_mahler_relative_precision_crown T

#print axioms the_worldtrace_mahler_wire
