import GSTTailFFourthDimension
import GSTGraphV2Ontological
import GSTGraphV2PowerThreeWaveObservation
import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE 4TH-DIMENSIONAL PROOF OF hTailF — the universe's machinery, assembled

THE separate proof file for the second-observer input
`four_power_omega_shadow_wave_tailF` — the statement the monolith's crown
consumes as `hTailF`.  The entire theorem machinery of the route is
assembled here, at the fourth dimension, where the proof of `hTailF` is
SEEN in a single screen.

The doctrine of the GST universe governs the assembly.  The space is
dimensionless: no dimension is added to it.  The fourth dimension here is
the sheet-invariant DIAGONAL (§2) — an axis that emerges, as an aftermath,
from the cube-lift chaos of the tower: the tower word stabilizes modulo
every window, the diagonal is the SAME object at every sheet level, and
one diagonal fire kills every sheet at once.  The observation law is
carried in BOTH of its faces: the conversion eyes (§1a, §1b — the trit
readings of the row word and the cut word, every depth, no window bound)
and THE WAVE FACE (§1c) — the GST observation law itself, where a Happy
cell on a power sheet with an all-depth bad boundary reappears as a
strictly positive coupled-U derivative: information propagates, never
dies.  The ontological current of the spacetime file rides with it (§1d):
Happy is exactly the positive sector of the twelve-cell certificate.

* **§1 THE OBSERVATION LAW** — both eyes, the wave face, the current.
* **§2 THE EMERGENT DIMENSION** — the diagonal: stabilization, descent,
  the kill; and the tower dodge of the package read AS the diagonal dodge.
* **§3 THE COMBINATION** — `theorem hTailF`, the proof visible in one
  screen: the two families of the input's witness through the two eyes.
* **§4 THE NEW LAWS APPLIED** — the level-six lattice: the cycle law and
  the identical proof on the thirty-four-survivor row law.
* **§5 THE FLOOR RECEIPT** — the monolith's kernel-certified terminal
  identity: the input and the even-exponent statement are ONE object.

Everything in this file is unconditional except the two named laws the
input still carries — `tailF_row_primitive` and `tailF_tower_primitive`,
stated as defs in the fourth-dimension chamber: the exact residual after
the Ω-tower, the Ω-sheet gate, the Ω-second-sheet gate, the sheet-zero
exponent-cycle gates, the diagonal blade and six lattice levels all fired
unconditionally.  §5 is the receipt for what those two laws carry: by the
kernel's own terminal identity (both directions machine-proven), the input
`four_power_omega_shadow_wave_tailF` and the even-exponent statement
`∀ K ≥ 8, noTernaryTwo (4^K) = false` are the same object — so the two
named laws carry exactly that content, and every OTHER theorem in this
file stands on proven theorems alone.
-/

namespace GSTTailFProof

open GSTCanonicalSevenAxisBridge
open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-! ## §1 The observation law — the two eyes, the wave face, the current

The row axis: `4 ^ core = 1 + 3^1 * omegaCutWord 0 core`, so the digit of
the power at position `1 + j` IS the row word's own trit at depth `j` —
every depth, no window.  The tower axis: `4 ^ (3^s * core) = 1 + 3^(s+1) *
omegaCutWord s core`, so the digit of the power at position `s+1+j` IS the
cut word's own trit at depth `j` — every depth, no window.  Whenever
either word fires its top third, the power owns its digit two: the words
are open books.  And the universe's own observation law — the wave face —
says the same thing in the physical graph: a Happy cell's information
reappears as a strictly positive coupled-U derivative, an all-depth bad
boundary notwithstanding.  The ontological current certifies the cell
itself: Happy is exactly the positive sector. -/

/-- **THE ROW EYE.**  Whenever the row word of `core` — the cut word at
sheet zero, `(4^core - 1)/3` — fires its top third at depth `j`, the power
`4 ^ core` owns its ternary digit two at position `1 + j`.  Unconditional. -/
theorem row_observation_law (core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2 :=
  omega_row_level_digit_two core j hkill

/-- **THE TOWER EYE.**  Whenever the cut word of the tower
`4 ^ (3^s * core)` fires its top third at depth `j` — at EVERY depth,
with no window bound, deep beyond the package's dodge band — the tower
power owns its ternary digit two at position `s+1+j`.
Unconditional. -/
theorem tower_observation_law (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2 :=
  tower_observation_digit_two s core j hkill

/-- **THE WAVE FACE — the GST observation law itself, advanced form.**
A Happy cell on the unit sheet of the power column, with an all-depth bad
boundary three x4 waves to its right, is not erased: it reappears as a
strictly positive coupled-U derivative while the exact width-three strip
equation and both phase signs remain live.  Information propagates, never
dies — the observation law of the universe, stated on the physical graph.
Unconditional. -/
theorem observation_law_wave :
    ∀ (K q : Nat),
      (GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.carry
        (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.digit) →
      (∀ j : Nat, ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.digit) →
      0 < GSTGraphV2PerfectPowerBlockProbe.graphPhaseWindow (4^K) 0 3 (q+1) ∧
        GSTGraphV2PerfectPowerBlockProbe.graphPhaseWindow (4^K) 3 3 (q+1) ≤ 0 ∧
        64 * (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.digit +
            GSTFinalPurePowerResidueTransplant.wideCarry 64 (4^K) (3+q) =
          (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+q)).seven.digit +
            3 * GSTFinalPurePowerResidueTransplant.wideCarry 64 (4^K) ((3+q)+1) ∧
        0 <
          3 * GSTGraphV2CoupledUFlux.potentialWith
              GSTGraphV2CoupledUFlux.gstUChargeExact (4^3)
              (GSTGraphV2UnifiedPowerRectangle.unifiedState (4^K) 3 ((3+q)+1)).core -
            GSTGraphV2CoupledUFlux.potentialWith
              GSTGraphV2CoupledUFlux.gstUChargeExact (4^3)
              (GSTGraphV2UnifiedPowerRectangle.unifiedState (4^K) 3 (3+q)).core :=
  GSTGraphV2PowerThreeWaveObservation.power_three_wave_observation

/-- **THE CURRENT — the ontological spacetime certificate.**  A physical
cell of the dimensionless graph is Happy exactly when its ontological
current is positive: the twelve-cell reverse-base-seven certificate of the
spacetime file, where the two Happy cells are the positive sector and
every bad cell is nonpositive.  Unconditional. -/
theorem universe_current_happy_iff (C d : Nat) (hC : C < 4) (hd : d < 3) :
    GSTU2DEventTransport.HappyCell C d ↔
      0 < GSTGraphV2Ontological.ontDensity C d :=
  GSTGraphV2Ontological.happy_iff_ontDensity_positive C d hC hd

/-- **THE NO-ERASURE WINDOW — the ontological current through the graph.**
A Happy source on the left edge of any nonzero-width production window
keeps the window's ontological current strictly positive: the leading
fire dominates the total worst-case mass of all lower rows under the
literal base-three vertical weighting.  Unconditional. -/
theorem universe_window_positive_of_happy (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : GSTU2DEventTransport.HappyCell
      (GSTGraphV2InfiniteControl.graph E 0 (b+q)).seven.carry
      (GSTGraphV2InfiniteControl.graph E 0 (b+q)).seven.digit) :
    0 < GSTGraphV2Ontological.graphOntWindow E N b (q+1) :=
  GSTGraphV2Ontological.graphOntWindow_positive_of_happy E N b q hN hHappy

/-! ## §2 The emergent dimension — the diagonal

The space is dimensionless; nothing is added.  The fourth dimension
EMERGES from the chaos of the cube lift: the cut word of sheet level
`s+1` is the cut word of level `s` plus a multiple of `3^(s+1)`, so every
trit below the lift is frozen as the sheet level grows — the tower word
at modulus `3^k` is the SAME object at every sheet level `s ≥ k-1`.  That
sheet-invariant object is the DIAGONAL.  One primitive diagonal trit two
kills the tower dodge at every sheet level at once: the dimension is an
aftermath of the chaos, and it carries the fire. -/

/-- **THE EMERGENCE — the cube-lift stabilization.**  The cut word of
sheet level `s+1` is the cut word of level `s` plus a multiple of
`3^(s+1)`: every trit below position `s+1` is frozen as the sheet level
grows.  The diagonal emerges here. -/
theorem emergent_dimension_stabilizes (s core : Nat) :
    ∃ t : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) * t :=
  omega_cut_word_stabilizes s core

/-- **THE EMERGENT AXIS — the descent to the primitive.**  For every
sheet level `s` at or above `k-1`, the tower word at modulus `3^k` is the
primitive level-`(k-1)` word: the diagonal is the SAME object at every
sheet. -/
theorem emergent_dimension_descent (core k : Nat) :
    ∀ s : Nat, k-1 ≤ s → (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k :=
  omega_tower_word_mod_chain core k

/-- **THE PACKAGE'S TOWER DODGE, READ AS THE DIAGONAL DODGE.**  Inside the
sheet's own window, the package's clause D constrains the tower word —
and the tower word IS the primitive diagonal there.  The fourth dimension
reads the package's dodge as one statement about the emergent axis. -/
theorem tower_dodge_is_diagonal_dodge (core s k : Nat) (hk : k ≤ s+1) :
    (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k :=
  omega_tower_word_mod_chain core k s (by omega)

/-- **THE KILL — one diagonal fire, every sheet.**  One ternary digit two
on the primitive diagonal at level `k-1` kills the tower dodge at EVERY
sheet level `S ≥ k-1` at once: the emergent dimension carries the fire
across the whole tower. -/
theorem emergent_dimension_kill (core k S : Nat)
    (hk1 : 1 ≤ k) (hkS : k ≤ S+1)
    (hTwo : digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2) :
    digit3 (4^(3^S * core)) (S + k) = 2 :=
  omega_tower_kill_of_diagonal_two core k S hk1 hkS hTwo

/-! ## §3 The combination — the proof of hTailF, seen from the fourth
dimension

The input hands us a witness `K = 3^s * core` with the full shadow
package.  Two families, two eyes, one proof:

* `s = 0` — the sheet-zero family.  The class clause leaves `core % 9`
  in `{1, 4}`, the row primitive fires the row word at some depth `j`,
  and the row eye converts the fire into the power's digit two at
  position `1 + j`.  Done.

* `s ≥ 1` — the tower family.  The class clause leaves `core % 9` in
  `{4, 7}`, the tower primitive — fed the package's own tower dodge,
  the all-depths window clause, which §2 reads as the diagonal dodge —
  fires the cut word's deep tail at some depth `i` beyond the dodge
  band, and the tower eye converts the fire into the power's digit two
  at position `s+1+i`.  Done.

The sheet gates (`hA`, `hB1`, `hB2`) and the row dodge (`hC`) of the
package are consumed by neither branch: the two named laws absorb
exactly the dodge structure and nothing else. -/

/-- **THE PROOF OF hTailF.**  The two named laws — the row primitive
and the tower primitive, the carried content of the input — compose,
through the two eyes of the observation law, into the full
second-observer input `four_power_omega_shadow_wave_tailF`. -/
theorem hTailF
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · -- SHEET-ZERO FAMILY: the row eye.
    -- The class clause pins the core for the row law.
    have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by
      rw [← hKsc]
      exact hK
    -- The row law fires the row word at some depth j ...
    obtain ⟨j, hj⟩ := hRow core hKc hfree hc14
    -- ... and the row eye converts the fire into the digit two.
    refine ⟨1+j, ?_⟩
    rw [hKsc]
    exact row_observation_law core j hj
  · -- TOWER FAMILY: the tower eye.
    -- The class clause pins the core for the tower law.
    have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    -- The tower law — fed the package's own all-depths dodge hD —
    -- fires the cut word's deep tail beyond the dodge band ...
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    -- ... and the tower eye converts the fire into the digit two.
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_law s core i hfire

/-! ## §4 The new laws applied — the same proof on the shrunk row law

The row lattice — the cycle laws of levels 27/81/243/729, the thirty
fired classes, the seventeen level-six fires, the thirty-four mod-729
survivors — closed 54 of the 81 hard-family classes unconditionally.
What remains carried by the row law shrunk to the survivor clause: the
proof of `hTailF` runs on it unchanged. -/

/-- **THE LEVEL-SIX CYCLE LAW** — the new law of the deepest lattice
level: the modulus-2187 residue of `4 ^ m` is pinned by the class of
`m` modulo 729. -/
theorem new_law_four_pow_mod2187 (m : Nat) :
    (4^m) % 2187 = (4^(m % 729)) % 2187 :=
  four_pow_mod2187 m

/-- **hTailF ON THE SHRUNK ROW LAW.**  The identical proof of
`hTailF`, running on the weaker hypothesis pair: the tower primitive
plus the thirty-four-survivor row primitive — the row law after the
lattice's six levels of unconditional fires.  The new laws shrink the
carried content; the proof does not move. -/
theorem hTailF_of_tower_and_row_mod729
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729) :
    four_power_omega_shadow_wave_tailF :=
  tailF_of_tower_and_row_mod729 hTower hRowMod

/-! ## §5 The floor receipt — what the two named laws carry

The monolith's kernel certifies the terminal identity in BOTH
directions: the second-observer input and the even-exponent Erdős
ternary statement are ONE object.  This is the floor receipt for the
two named laws of §3: they are the exact residual of the input after
the entire machinery fired, and their content is the even-exponent
statement itself.  Everything else in this file stands on proven
theorems only. -/

/-- **THE TERMINAL IDENTITY, CARRIED INTO THE PROOF FILE.**  The input
`four_power_omega_shadow_wave_tailF` and the even-exponent statement
`∀ K ≥ 8, noTernaryTwo (4^K) = false` are the same object, both
directions machine-proven by the monolith's kernel. -/
theorem hTailF_iff_even_conjecture :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  erdos_even_conjecture_iff_tailF.symm

#print axioms row_observation_law
#print axioms tower_observation_law
#print axioms observation_law_wave
#print axioms universe_current_happy_iff
#print axioms universe_window_positive_of_happy
#print axioms emergent_dimension_stabilizes
#print axioms emergent_dimension_descent
#print axioms tower_dodge_is_diagonal_dodge
#print axioms emergent_dimension_kill
#print axioms hTailF
#print axioms new_law_four_pow_mod2187
#print axioms hTailF_of_tower_and_row_mod729
#print axioms hTailF_iff_even_conjecture

end GSTTailFProof
