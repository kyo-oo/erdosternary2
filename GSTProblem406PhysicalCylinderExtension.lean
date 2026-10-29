import GSTFourPowerAffineOntologicalCompleteness
import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Physical CommonTwo is dense in every finite exponent cylinder

This is an UNCONDITIONAL theorem about real four-power exponents.
The result does not assert that every individual exponent is good:
the cylinder witness may vary with the prefix length.

A finite ternary source word of length p can be extended with TWO
consecutive digits 2. For any carry c in {0,1,2,3}, multiplying
the new source by 4 and adding 1 gives a common two in one of
those two new positions. The exact affine prefix isometry then
realizes the extended source word by a real 4^K exponent congruent
to the originally prescribed exponent mod 3^p.
-/

namespace GSTProblem406PhysicalCylinderExtension

open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineOntologicalCompleteness

/-- Two high ternary digits 2 in the source force a source-neighbor
collision at one of those very two positions, regardless of the
incoming base-three carry. -/
theorem two_twos_force_pair (p r : Nat) (hr : r < 3^p) :
    let X := r + 3^p * 8
    digit3 X p = 2 ∧
    digit3 X (p+1) = 2 ∧
    (digit3 (4*X+1) p = 2 ∨
     digit3 (4*X+1) (p+1) = 2) := by
  dsimp only
  let X := r + 3^p*8
  have hN : 0 < 3^p := by positivity
  have hsourceQ : X / 3^p = 8 := by
    dsimp [X]
    rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hr]
  have hneighbor : 4*X+1 = (4*r+1)+3^p*32 := by
    dsimp [X]
    ring
  have hneighborQ :
      (4*X+1) / 3^p = (4*r+1)/3^p+32 := by
    rw [hneighbor, Nat.add_mul_div_left _ _ hN]
  have hcarry : (4*r+1)/3^p < 4 := by
    apply (Nat.div_lt_iff_lt_mul hN).2
    omega
  have hchoice :
      ((4*r+1)/3^p+32)%3=2 ∨
      (((4*r+1)/3^p+32)/3)%3=2 := by
    have four_cases (c : Nat) (hc : c < 4) :
        c=0 ∨ c=1 ∨ c=2 ∨ c=3 := by omega
    have hc := four_cases ((4*r+1)/3^p) hcarry
    rcases hc with h0 | h1 | h2 | h3
    · left
      norm_num [h0]
    · right
      norm_num [h1]
    · right
      norm_num [h2]
    · left
      norm_num [h3]
  have hlow : digit3 X p = 2 := by
    unfold digit3
    rw [hsourceQ]
  have hhigh : digit3 X (p+1) = 2 := by
    unfold digit3
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hsourceQ]
  refine ⟨hlow,hhigh,?_⟩
  rcases hchoice with h | h
  · left
    unfold digit3
    rw [hneighborQ]
    exact h
  · right
    unfold digit3
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hneighborQ]
    exact h

private theorem digit_eq_from_prefix
    (p R S j : Nat) (hj : j < p)
    (hmod : R%3^p=S%3^p) :
    digit3 R j = digit3 S j := by
  have hdiv : 3^(j+1) ∣ 3^p :=
    Nat.pow_dvd_pow 3 (by omega)
  apply digit3_eq_of_mod_next
  calc
    R%3^(j+1) = (R%3^p)%3^(j+1) :=
      (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (S%3^p)%3^(j+1) := by rw [hmod]
    _ = S%3^(j+1) := Nat.mod_mod_of_dvd _ hdiv

/-- Every 3-adic exponent cylinder contains a genuine power-of-four
pair with a common 2, with witness at physical row p+1 or p+2.
The successful exponent is CONGRUENT to the prescribed exponent
K modulo 3^p: this is not a generic surrogate. -/
theorem every_exponent_cylinder_contains_physical_common_two
    (p K : Nat) :
    ∃ K' : Nat, K'%3^p=K%3^p ∧
      ((digit3 (4^K') (p+1)=2 ∧
        digit3 (4^(K'+1)) (p+1)=2) ∨
       (digit3 (4^K') (p+2)=2 ∧
        digit3 (4^(K'+1)) (p+2)=2)) := by
  let r := affineOrbit K % 3^p
  let X := r+3^p*8
  have hr : r < 3^p := Nat.mod_lt _ (by positivity)
  have hX_lt : X < 3^(p+2) := by
    have hp : 3^(p+2) = 3^p*9 := by rw [pow_add]; norm_num
    dsimp [X]
    rw [hp]
    omega
  obtain ⟨K',hK',hmod⟩ :=
    every_affine_prefix_is_physical (p+2) X hX_lt
  have hmodFull : affineOrbit K'%3^(p+2)=X%3^(p+2) := by
    simpa [Nat.mod_eq_of_lt hX_lt] using hmod
  have hdiv : 3^p ∣ 3^(p+2) :=
    Nat.pow_dvd_pow 3 (by omega)
  have hpre : affineOrbit K'%3^p=X%3^p := by
    calc
      affineOrbit K'%3^p =
          (affineOrbit K'%3^(p+2))%3^p :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (X%3^(p+2))%3^p := by rw [hmodFull]
      _ = X%3^p := Nat.mod_mod_of_dvd _ hdiv
  have hXmod : X%3^p=affineOrbit K%3^p := by
    dsimp [X,r]
    simp [Nat.add_mod, Nat.mul_mod]
  have hexp : K'%3^p=K%3^p :=
    (affineOrbit_residue_eq_iff_exponent_residue_eq p K' K).mp
      (hpre.trans hXmod)
  have hsourceModeq :
      affineOrbit K' ≡ X [MOD 3^(p+2)] := hmodFull
  have hneighborModeq :
      4*affineOrbit K'+1 ≡ 4*X+1 [MOD 3^(p+2)] := by
    have h := (hsourceModeq.mul_left 4).add_left 1
    simpa only [Nat.add_comm] using h
  have htail (j : Nat) (hj : j<p+2) :
      digit3 (affineOrbit K') j = digit3 X j ∧
      digit3 (affineOrbit (K'+1)) j =
        digit3 (4*X+1) j := by
    constructor
    · exact digit_eq_from_prefix (p+2) _ _ j hj hmodFull
    · rw [affineOrbit_succ]
      exact digit_eq_from_prefix (p+2) _ _ j hj hneighborModeq
  obtain ⟨hlow,hhigh,hchoice⟩ := two_twos_force_pair p r hr
  refine ⟨K',hexp,?_⟩
  rcases hchoice with hl | hh
  · left
    have ht := htail p (by omega)
    constructor
    · rw [four_pow_digit_affine_shift K' p, ht.1]
      exact hlow
    · rw [four_pow_digit_affine_shift (K'+1) p, ht.2]
      exact hl
  · right
    have ht := htail (p+1) (by omega)
    constructor
    · rw [show p+2=(p+1)+1 by omega,
        four_pow_digit_affine_shift K' (p+1), ht.1]
      exact hhigh
    · rw [show p+2=(p+1)+1 by omega,
        four_pow_digit_affine_shift (K'+1) (p+1), ht.2]
      exact hh

#print axioms two_twos_force_pair
#print axioms every_exponent_cylinder_contains_physical_common_two

end GSTProblem406PhysicalCylinderExtension
