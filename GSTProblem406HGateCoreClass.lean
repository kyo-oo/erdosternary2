import GSTOmegaResidueClassExit
import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Targeted hGate discharge route: direct infinite CommonTwo classes

Unlike the previous source-only digit-two certificates, this module proves
a SAME-ROW digit two in 4^K AND 4^(K+1), which is the precise
GSTFourPowerDirectExistence.CommonTwo / third-wave gate assertion.

For every L>=6 and unbounded u with u%3 !=0, this proof covers 11
of the 18 core classes modulo 27. No upper bound on u or L.
The remaining seven classes are not asserted impossible.
-/

namespace GSTProblem406HGateCoreClass

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Exact neighbor wave: 4^5=1024 is below 3^(L+1) for L>=6,
so the first three new quotient digits are 22u mod27. -/
theorem neighbor_quotient_mod27
    (L u : Nat) (hL : 6 ≤ L) :
    (4^(5+u*3^L)/3^(L+1))%27=(22*u)%27 := by
  have hsmall : (4:Nat)^5 < 3^(L+1) := by
    have hnum : (4:Nat)^5 < 3^7 := by decide
    have hpow : 3^7 ≤ 3^(L+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hdiv : (4:Nat)^5/3^(L+1)=0 :=
    Nat.div_eq_of_lt hsmall
  have h1024 : (1024:Nat)/3^(L+1)=0 := by
    simpa only [show (4:Nat)^5=1024 by decide] using hdiv
  have h := GSTWorldtraceBlockLift.pow4_whole_block_lift
    5 u L 3 (by omega) (by omega)
  have hblock :
      (4^(5+u*3^L)/3^(L+1))%27 =
        (u*GSTCanonicalTailLTE.lteCoeff L*1024)%27 := by
    simpa only [show (3:Nat)^3=27 by decide,
      show (4:Nat)^5=1024 by decide,
      h1024, Nat.zero_add] using h
  have hc : (GSTCanonicalTailLTE.lteCoeff L*1024)%27=22 := by
    rw [Nat.mul_mod,
      GSTOmegaExactDelayedEscape.lteCoeff_mod27_sixteen L (by omega)] <;> decide
  calc
    (4^(5+u*3^L)/3^(L+1))%27 =
      (u*GSTCanonicalTailLTE.lteCoeff L*1024)%27 := hblock
    _ = (u*(GSTCanonicalTailLTE.lteCoeff L*1024))%27 := by ring
    _ = (u*22)%27 := by
      calc
        (u*(GSTCanonicalTailLTE.lteCoeff L*1024))%27 =
          ((u%27)*((GSTCanonicalTailLTE.lteCoeff L*1024)%27))%27 :=
            Nat.mul_mod _ _ _
        _ = ((u%27)*22)%27 := by rw [hc]
        _ = (u*22)%27 := by
          simpa using (Nat.mul_mod u 22 27).symm
    _ = (22*u)%27 := by ac_rfl

/-- The neighbor's actual p=L+1+k ternary digit equals a trit of 22u. -/
theorem neighbor_three_digit_bridge
    (L u k : Nat) (hL : 6 ≤ L) (hk : k < 3) :
    digit3 (4^(5+u*3^L)) (L+1+k) = digit3 (22*u) k := by
  have hmod27 := neighbor_quotient_mod27 L u hL
  have hdiv : 3^(k+1) ∣ 27 := by
    have hp : 3^(k+1) ∣ 3^3 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^3=27 by decide] using hp
  have hmod :
      (4^(5+u*3^L)/3^(L+1))%3^(k+1) =
        (22*u)%3^(k+1) := by
    calc
      (4^(5+u*3^L)/3^(L+1))%3^(k+1) =
        ((4^(5+u*3^L)/3^(L+1))%27)%3^(k+1) :=
          (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((22*u)%27)%3^(k+1) := by rw [hmod27]
      _ = (22*u)%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  have hread := digit3_eq_of_mod_next
      (4^(5+u*3^L)/3^(L+1)) (22*u) k hmod
  calc
    digit3 (4^(5+u*3^L)) (L+1+k) =
      digit3 (4^(5+u*3^L)/3^(L+1)) k := by
        unfold digit3
        have hp : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (22*u) k := hread

/-- Exact finite-residue classifier, universally valid for any unbounded
u in a certified residue class. -/
private theorem eleven_of_eighteen_kernel :
    ∀ r : Fin 27,
      r.val%3≠0 →
      r.val≠4 → r.val≠10 → r.val≠13 →
      r.val≠16 → r.val≠19 → r.val≠22 → r.val≠25 →
      ∃ k : Fin 3,
        digit3 (19*r.val) k.val=2 ∧
        digit3 (22*r.val) k.val=2 := by decide

private theorem same_digit_mul_mod27
    (u m k : Nat) (hk : k<3) :
    digit3 (m*u) k = digit3 (m*(u%27)) k := by
  have hdiv : 3^(k+1) ∣ 27 := by
    have hp : 3^(k+1) ∣ 3^3 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^3=27 by decide] using hp
  have hbig : (m*u)%27=(m*(u%27))%27 := by
    simp [Nat.mul_mod]
  have hmod : (m*u)%3^(k+1)=(m*(u%27))%3^(k+1) := by
    calc
      (m*u)%3^(k+1)=((m*u)%27)%3^(k+1) :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((m*(u%27))%27)%3^(k+1) := by rw [hbig]
      _ = (m*(u%27))%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  exact digit3_eq_of_mod_next _ _ k hmod

/-- The gate itself, proved for eleven whole residue classes of unbounded
exponents K=4+u3^L, not a weaker source-only digit-two statement. -/
theorem commonTwo_unbounded_core_classes
    (L u : Nat) (hL : 6≤L) (h3 : u%3≠0)
    (h4 : u%27≠4) (h10 : u%27≠10)
    (h13 : u%27≠13) (h16 : u%27≠16)
    (h19 : u%27≠19) (h22 : u%27≠22)
    (h25 : u%27≠25) :
    CommonTwo (4+u*3^L) := by
  let r : Fin 27 := ⟨u%27, Nat.mod_lt _ (by decide)⟩
  have hr3 : r.val%3≠0 := by
    have h : (u%27)%3 = u%3 :=
      Nat.mod_mod_of_dvd u (by decide : 3 ∣ 27)
    dsimp [r]
    rw [h]
    exact h3
  obtain ⟨k,hpair⟩ :=
    eleven_of_eighteen_kernel r hr3 h4 h10 h13 h16 h19 h22 h25
  have hsource : digit3 (19*u) k.val=2 := by
    rw [same_digit_mul_mod27 u 19 k.val k.isLt]
    exact hpair.1
  have hneighbor : digit3 (22*u) k.val=2 := by
    rw [same_digit_mul_mod27 u 22 k.val k.isLt]
    exact hpair.2
  refine ⟨L+1+k.val, by omega, ?_, ?_⟩
  · rw [show 4+u*3^L=4+u*3^L by rfl]
    rw [GSTOmegaResidueClassExit.three_trit_digit_bridge L u k.val
      (by omega) k.isLt]
    exact hsource
  · have hexp : (4+u*3^L)+1 = 5+u*3^L := by omega
    rw [hexp, neighbor_three_digit_bridge L u k.val hL k.isLt]
    exact hneighbor

#print axioms neighbor_quotient_mod27
#print axioms neighbor_three_digit_bridge
#print axioms eleven_of_eighteen_kernel
#print axioms commonTwo_unbounded_core_classes

end GSTProblem406HGateCoreClass
