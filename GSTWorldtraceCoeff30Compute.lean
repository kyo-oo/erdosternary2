import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact kernel-verifiable GST coefficient c_29 modulo 3^30
Never expand the huge number 4^(3^29). Instead propagate a tiny modular
coefficient by the exact GST cubic recursion and a polynomial congruence law.
-/
namespace GSTWorldtraceCoeff30Compute

open GSTCanonicalTailLTE

def modulus : Nat := 3^30

def residueCoeff : Nat → Nat
 | 0 => 1
 | n+1 =>
   let x := residueCoeff n
   (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus

private theorem polynomial_mod (n x y : Nat)
    (h : x%modulus=y%modulus) :
    (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus =
    (y+3^(n+1)*y^2+3^(2*n+1)*y^3)%modulus := by
  have hp2 : (x^2)%modulus=(y^2)%modulus := by
    calc
      (x^2)%modulus = ((x%modulus)^2)%modulus := Nat.pow_mod x 2 modulus
      _ = ((y%modulus)^2)%modulus := by rw [h]
      _ = (y^2)%modulus := (Nat.pow_mod y 2 modulus).symm
  have hp3 : (x^3)%modulus=(y^3)%modulus := by
    calc
      (x^3)%modulus = ((x%modulus)^3)%modulus := Nat.pow_mod x 3 modulus
      _ = ((y%modulus)^3)%modulus := by rw [h]
      _ = (y^3)%modulus := (Nat.pow_mod y 3 modulus).symm
  have hm2 : (3^(n+1)*x^2)%modulus =
      (3^(n+1)*y^2)%modulus := by
    calc
      (3^(n+1)*x^2)%modulus =
          ((3^(n+1)%modulus)*(x^2%modulus))%modulus :=
        Nat.mul_mod _ _ _
      _ = ((3^(n+1)%modulus)*(y^2%modulus))%modulus := by rw [hp2]
      _ = (3^(n+1)*y^2)%modulus := (Nat.mul_mod _ _ _).symm
  have hm3 : (3^(2*n+1)*x^3)%modulus =
      (3^(2*n+1)*y^3)%modulus := by
    calc
      (3^(2*n+1)*x^3)%modulus =
          ((3^(2*n+1)%modulus)*(x^3%modulus))%modulus :=
        Nat.mul_mod _ _ _
      _ = ((3^(2*n+1)%modulus)*(y^3%modulus))%modulus := by rw [hp3]
      _ = (3^(2*n+1)*y^3)%modulus := (Nat.mul_mod _ _ _).symm
  have hsum2 :
      (x+3^(n+1)*x^2)%modulus =
      (y+3^(n+1)*y^2)%modulus := by
    calc
      (x+3^(n+1)*x^2)%modulus =
        ((x%modulus)+(3^(n+1)*x^2)%modulus)%modulus :=
          Nat.add_mod _ _ _
      _ = ((y%modulus)+(3^(n+1)*y^2)%modulus)%modulus := by
        rw [h, hm2]
      _ = (y+3^(n+1)*y^2)%modulus := (Nat.add_mod _ _ _).symm
  calc
    (x+3^(n+1)*x^2+3^(2*n+1)*x^3)%modulus =
      (((x+3^(n+1)*x^2)%modulus)+
       (3^(2*n+1)*x^3)%modulus)%modulus := Nat.add_mod _ _ _
    _ = (((y+3^(n+1)*y^2)%modulus)+
       (3^(2*n+1)*y^3)%modulus)%modulus := by rw [hsum2, hm3]
    _ = (y+3^(n+1)*y^2+3^(2*n+1)*y^3)%modulus :=
       (Nat.add_mod _ _ _).symm

theorem residue_coeff_correct (n : Nat) :
    residueCoeff n = lteCoeff n%modulus := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have h : residueCoeff n%modulus=lteCoeff n%modulus := by
        rw [ih]
        simp only [Nat.mod_mod]
      have hp := polynomial_mod n (residueCoeff n) (lteCoeff n) h
      change
        (residueCoeff n +3^(n+1)*(residueCoeff n)^2+
          3^(2*n+1)*(residueCoeff n)^3)%modulus =
        (lteCoeff n +3^(n+1)*(lteCoeff n)^2+
          3^(2*n+1)*(lteCoeff n)^3)%modulus
      exact hp

/-- A finite 30-step modular-recurrence computation, not huge raw powers. -/
theorem residue_coeff29 :
    residueCoeff 29 = 28881270545965 := by decide

/-- Fully kernel-certified GST stable-coefficient value c_29 modulo 3^30. -/
theorem coeff29_exact_mod18 :
    lteCoeff 29 % 3^30 = 28881270545965 := by
  calc
    lteCoeff 29 % 3^30 = residueCoeff 29 :=
      (residue_coeff_correct 29).symm
    _ = 28881270545965 := residue_coeff29

#print axioms residue_coeff_correct
#print axioms residue_coeff29
#print axioms coeff29_exact_mod18

end GSTWorldtraceCoeff30Compute
