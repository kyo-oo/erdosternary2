import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
# GST 406: rigorous cross-radix finite-binary-residue no-go law

This is a source-EXACT, UNBOUNDED obstruction to the proposed
"four carry states x fixed binary residue modulo 2^T" closure.

For every natural T, the explicitly constructed natural number
  R = 1 + 9 + 9^2 + ... + 9^(2^T-1)
is a positive ternary-1-unit, is divisible by 2^T, yet its 4R
has no ternary digit 2 AT ANY ROW.

Proof mechanisms:
  8*R+1=9^(2^T), and 4R=(3^(2*(2^T))-1)/2,
  which is an all-ones base-three repunit.
  R_(2m)=R_m*(1+9^m), so R_(2^T) is divisible by 2^T.

This refutes any attempt to derive collision from a fixed amount
of binary residue information plus the source's base-three carry-1
entry state. It does NOT refute the much stronger source-specific
origin R=4^K with a binary valuation LINEAR in ternary length,
and it does NOT prove or refute the full Erdős conjecture.
-/

namespace GSTProblem406MathboxBinaryResidueNoGo

open GSTFourPowerDirectResidue

/-- Base-three repunit containing n copies of digit 1. -/
def repunit3 : Nat → Nat
  | 0 => 0
  | n+1 => 3*repunit3 n+1

/-- Sparse ternary word with digits 1 on even rows and 0 on odd rows. -/
def sparseOne3 : Nat → Nat
  | 0 => 0
  | n+1 => sparseOne3 n+9^n

/-- Two-times the repunit plus one is the appropriate power of 3. -/
theorem repunit3_closed (n : Nat) :
    2*repunit3 n+1 = 3^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [repunit3, pow_succ]
      omega

/-- Eight-times the sparse word plus one is the appropriate power of 9. -/
theorem sparseOne3_closed (n : Nat) :
    8*sparseOne3 n+1 = 9^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [sparseOne3, pow_succ]
      omega

/-- Exact identity: 4 times the sparse word has EVERY ternary digit 1
until row 2n, then only zeros. -/
theorem four_sparse_is_ternary_repunit (n : Nat) :
    4*sparseOne3 n = repunit3 (2*n) := by
  have hs := sparseOne3_closed n
  have hr := repunit3_closed (2*n)
  have hp : (3:Nat)^(2*n)=9^n := by
    rw [pow_mul]
    norm_num
  omega

private theorem digit3_three_scale_zero (x : Nat) :
    digit3 (3*x+1) 0=1 := by
  simp [digit3, Nat.add_mod, Nat.mul_mod]

private theorem digit3_three_scale_succ (x p : Nat) :
    digit3 (3*x+1) (p+1)=digit3 x p := by
  unfold digit3
  have hdiv : (3*x+1)/3=x := by omega
  rw [show (3:Nat)^(p+1)=3*3^p by
      rw [pow_succ]
      omega,
      ← Nat.div_div_eq_div_mul, hdiv]

/-- For every natural length, no digit of a base-three repunit is 2. -/
theorem repunit3_no_two (n p : Nat) :
    digit3 (repunit3 n) p ≠ 2 := by
  induction n generalizing p with
  | zero =>
      simp [repunit3, digit3]
  | succ n ih =>
      cases p with
      | zero =>
          change digit3 (3*repunit3 n+1) 0 ≠ 2
          rw [digit3_three_scale_zero]
          decide
      | succ p =>
          change digit3 (3*repunit3 n+1) (p+1) ≠ 2
          rw [digit3_three_scale_succ]
          exact ih p

/-- Every sparse ternary word is BAD because its 4x neighbor has
no ternary digit 2 anywhere. -/
theorem four_sparse_no_two (n p : Nat) :
    digit3 (4*sparseOne3 n) p ≠ 2 := by
  rw [four_sparse_is_ternary_repunit]
  exact repunit3_no_two (2*n) p

/-- Exact doubling relation; this builds arbitrarily high binary
divisibility while PRESERVING the BAD ternary structure. -/
theorem sparseOne3_double (m : Nat) :
    sparseOne3 (2*m) = sparseOne3 m*(9^m+1) := by
  have h2 := sparseOne3_closed (2*m)
  have h1 := sparseOne3_closed m
  have hp : (9:Nat)^(2*m)=9^m*9^m := by
    rw [show 2*m=m+m by omega, pow_add]
  have hsame : 8*(sparseOne3 m*(9^m+1))+1=9^m*9^m := by
    rw [← h1]
    ring
  have hres : 8*sparseOne3 (2*m)+1 =
      8*(sparseOne3 m*(9^m+1))+1 := by
    calc
      8*sparseOne3 (2*m)+1 = 9^(2*m) := h2
      _ = 9^m*9^m := hp
      _ = 8*(sparseOne3 m*(9^m+1))+1 := hsame.symm
  omega

/-- For every binary precision T, a sparse BAD source survives
while being divisible by 2^T. -/
theorem arbitrary_binary_precision_divides_sparse
    (T : Nat) :
    (2:Nat)^T ∣ sparseOne3 (2^T) := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      have heven : 2 ∣ ((9:Nat)^(2^T)+1) := by
        have hmod : ((9:Nat)^(2^T))%2=1 := by
          simp [Nat.pow_mod]
        omega
      obtain ⟨a,ha⟩ := ih
      obtain ⟨b,hb⟩ := heven
      refine ⟨a*b, ?_⟩
      calc
        sparseOne3 (2^(T+1)) =
            sparseOne3 (2*(2^T)) := by
              congr 1
              rw [pow_succ]
              omega
        _ = sparseOne3 (2^T)*(9^(2^T)+1) :=
            sparseOne3_double (2^T)
        _ = (2^T*a)*(2*b) := by rw [ha,hb]
        _ = 2^(T+1)*(a*b) := by rw [pow_succ]; ring

/-- The source begins at ternary carry state one, exactly matching
the physical source 4^K modulo three. -/
theorem sparseOne3_mod3_one
    (m : Nat) (hm : 0 < m) :
    sparseOne3 m%3=1 := by
  have hc := sparseOne3_closed m
  have hp : (9:Nat)^m%3=0 := by
    cases m with
    | zero => omega
    | succ m =>
        simp [pow_succ, Nat.mul_mod]
  omega

/-- The exact obstruction to the proposed fixed-precision product-state
proof route. The existential BAD source is constructed for every T,
not extrapolated from finite searches. -/
theorem bad_sources_at_arbitrarily_high_binary_precision
    (T : Nat) :
    ∃ R : Nat,
       0<R ∧ R%3=1 ∧ (2:Nat)^T ∣ R ∧
       ∀ p : Nat, 1 ≤ p →
       ¬ (digit3 R p = 2 ∧ digit3 (4*R) p=2) := by
  refine ⟨sparseOne3 (2^T), ?_, ?_, ?_, ?_⟩
  · have hc := sparseOne3_closed (2^T)
    have hp : 1 < (9:Nat)^(2^T) := by
      have ht : 0<(2:Nat)^T := by positivity
      cases hcase : (2:Nat)^T with
      | zero => omega
      | succ n =>
          have hn : 0 < (9:Nat)^n := by positivity
          rw [pow_succ]
          omega
    omega
  · exact sparseOne3_mod3_one (2^T) (by positivity)
  · exact arbitrary_binary_precision_divides_sparse T
  · intro p hp hbad
    exact four_sparse_no_two (2^T) p hbad.2

/-- Exact general-source collision proposition. Unlike physical 4^K,
this predicate permits every natural source R. -/
def GenericCommonTwo (R : Nat) : Prop :=
  ∃ p : Nat, 1 ≤ p ∧
    digit3 R p=2 ∧ digit3 (4*R) p=2

/-- FORMAL IMPOSSIBILITY of any proposed universal separator using ONLY
entry carry 1 and a fixed binary congruence at precision T:
such a separator would contradict the explicit infinite BAD family.
This is a proved negation of the weaker surrogate bridge, not
a negation of the original genuine perfect-power theorem. -/
theorem fixed_precision_does_not_force_generic_collision
    (T : Nat) :
    ¬ (∀ R : Nat, 0 < R → R%3=1 →
       (2:Nat)^T ∣ R → GenericCommonTwo R) := by
  intro hsep
  obtain ⟨R,hpos,hmod,hdiv,hbad⟩ :=
    bad_sources_at_arbitrarily_high_binary_precision T
  obtain ⟨p,hp,hs,hn⟩ := hsep R hpos hmod hdiv
  exact hbad p hp ⟨hs,hn⟩

#print axioms fixed_precision_does_not_force_generic_collision

#print axioms repunit3_closed
#print axioms sparseOne3_closed
#print axioms four_sparse_is_ternary_repunit
#print axioms repunit3_no_two
#print axioms four_sparse_no_two
#print axioms sparseOne3_double
#print axioms arbitrary_binary_precision_divides_sparse
#print axioms sparseOne3_mod3_one
#print axioms bad_sources_at_arbitrarily_high_binary_precision

end GSTProblem406MathboxBinaryResidueNoGo
