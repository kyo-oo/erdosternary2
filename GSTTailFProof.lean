import GSTTailFFourthDimension
import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE 4TH-DIMENSIONAL PROOF OF hTailF

THE separate proof file for the second-observer input
`four_power_omega_shadow_wave_tailF` — the statement the monolith's
crown consumes as `hTailF`.  The entire theorem machinery of the route
— the observation law, the combinations, the new laws — assembled in
ONE file, at the fourth dimension, where the proof of `hTailF` is
SEEN in a single screen:

* **§1 THE OBSERVATION LAW — the two eyes.**  The row eye reads the
  digits of `4 ^ core` off the row word at every depth; the tower eye
  reads the digits of `4 ^ (3^s * core)` off the cut word at EVERY
  depth — no window bound.  A top-third fire in either word IS a
  ternary digit two of the power itself: the conversion is
  unconditional, nothing carried.

* **§2 THE COMBINATION — the proof of `hTailF`, visible.**  The
  input's witness `K = 3^s * core` splits into the sheet-zero family
  (the row eye) and the tower family (the tower eye).  The two named
  laws — the row primitive and the tower primitive, the carried
  content of the input, stated as defs in the fourth-dimension
  chamber — compose into the full input.  The sheet gates and the row
  dodge of the shadow package pass through untouched: the named laws
  absorb exactly the dodge structure and nothing else.

* **§3 THE NEW LAWS APPLIED.**  The level-six lattice — the cycle law
  `4 ^ m % 2187 = 4 ^ (m % 729) % 2187`, the seventeen fires, the
  thirty-four survivors — shrinks the row law's carried content: the
  same proof of `hTailF` runs unchanged on the weaker hypothesis pair
  (tower primitive + thirty-four-survivor row primitive).

Zero monolith bytes touched.  Zero chamber bytes touched.  Everything
in this file is unconditional except the two named laws, which enter
as hypotheses — the input's exact residual, disclosed at every
surface, exactly as the chamber discloses them.
-/

namespace GSTTailFProof

open GSTCanonicalSevenAxisBridge
open GSTGraphV2OmegaWaveLaw
open GSTTailFFourthDimension

/-! ## §1 The observation law — the two eyes of the fourth dimension

One law per axis.  The row axis: `4 ^ core = 1 + 3^1 * omegaCutWord 0
core`, so the digit of the power at position `1 + j` IS the row word's
own trit at depth `j` — every depth, no window.  The tower axis:
`4 ^ (3^s * core) = 1 + 3^(s+1) * omegaCutWord s core`, so the digit
of the power at position `s+1+j` IS the cut word's own trit at depth
`j` — every depth, no window, positions far beyond the package's
dodge band.  Whenever either word fires its top third, the power owns
its digit two.  These two conversions are the whole fourth-dimension
view: the words are open books. -/

/-- **THE ROW EYE.**  Whenever the row word of `core` — the cut word
at sheet zero, `(4^core - 1)/3` — fires its top third at depth `j`,
the power `4 ^ core` owns its ternary digit two at position `1 + j`.
Unconditional. -/
theorem row_observation_law (core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2 :=
  omega_row_level_digit_two core j hkill

/-- **THE TOWER EYE.**  Whenever the cut word of the tower
`4 ^ (3^s * core)` fires its top third at depth `j` — at EVERY depth,
with no window bound, deep beyond the package's dodge band — the
tower power owns its ternary digit two at position `s+1+j`.
Unconditional. -/
theorem tower_observation_law (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2 :=
  tower_observation_digit_two s core j hkill

/-! ## §2 The combination — the proof of hTailF, seen from the fourth
dimension

The input hands us a witness `K = 3^s * core` with the full shadow
package.  Two families, two eyes, one proof:

* `s = 0` — the sheet-zero family.  The class clause leaves `core % 9`
  in `{1, 4}`, the row primitive fires the row word at some depth `j`,
  and the row eye converts the fire into the power's digit two at
  position `1 + j`.  Done.

* `s ≥ 1` — the tower family.  The class clause leaves `core % 9` in
  `{4, 7}`, the tower primitive — fed the package's own tower dodge,
  the all-depths window clause — fires the cut word's deep tail at
  some depth `i` beyond the dodge band, and the tower eye converts
  the fire into the power's digit two at position `s+1+i`.  Done.

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

/-! ## §3 The new laws applied — the same proof on the shrunk row law

The row lattice — the cycle laws of levels 27/81/243/729, the thirty
fired classes, the seventeen level-six fires, the thirty-four
mod-729 survivors — closed 54 of the 81 hard-family classes
unconditionally.  What remains carried by the row law shrunk to the
survivor clause: the proof of `hTailF` runs on it unchanged. -/

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

#print axioms row_observation_law
#print axioms tower_observation_law
#print axioms hTailF
#print axioms new_law_four_pow_mod2187
#print axioms hTailF_of_tower_and_row_mod729

end GSTTailFProof
