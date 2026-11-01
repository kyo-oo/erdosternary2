/-
  ERDŐS PROBLEM #261 — THE GREEDY WALK THEOREM
  ============================================
  Lean 4 core only (toolchain leanprover/lean4:v4.33.0-rc2, NO Mathlib).

  THE PROBLEM (Erdős, Er88c; erdosproblems.com/261 — OPEN):
    Is it true for ALL n ≥ 1 that there exist an integer t ≥ 2 and DISTINCT
    integers a_1 < a_2 < ... < a_t with
        n / 2^n  =  Σ_{k=1..t}  a_k / 2^{a_k} ?
    (Tengely–Ulas–Zygadlo, arXiv:2008.01501 verified n ≤ 10^4 by greedy.)

  THE GREEDY WALK (decoded from TUZ20; formalized here core-only):
    State (N, v) with 0 ≤ v < N.
    Step: if 2*v ≥ N then v ← 2*v − N (TAKE piece N), else v ← 2*v;
    then N ← N + 1.  Equivalently  v_{N+1} = (2 * v_N) mod N.
    Start: (n+1, n) for n ≥ 2 ; (3, 2) for n = 1.  TERMINATION: v = 0.
    The taken indices form the witness set S.

  MAIN THEOREM (kernel-checked):
    If the walk from n terminates at (N, 0) with taken list S, then
        Σ_{a ∈ S}  a * 2^(N − a)  =  n * 2^(N − n),
    every a ∈ S is < N, and |S| ≥ 2 whenever n ≥ 2.
    Dividing by 2^N yields exactly the #261 representation
        n / 2^n = Σ_{a ∈ S} a / 2^a
    (division performed in DERIVATION.md; the integer identity above
    IS the machine certificate).

  Axiom footprint: [propext, Quot.sound] only — no sorryAx, no choice.
-/

/-- Weighted sum: Σ_{a ∈ l} a * 2^(N − a). Right fold, core only. -/
def wsum (N : Nat) (l : List Nat) : Nat :=
  l.foldr (fun (a : Nat) (acc : Nat) => a * 2^(N - a) + acc) 0

theorem wsum_nil (N : Nat) : wsum N [] = 0 := rfl

theorem wsum_cons (N a : Nat) (l : List Nat) :
    wsum N (a :: l) = a * 2^(N - a) + wsum N l := rfl

/-- Doubling lemma: raising the scale N by one doubles the weighted sum
    (valid when every index is ≤ N, so exponents behave). -/
theorem wsum_shift : ∀ (S : List Nat) (N : Nat), (∀ a ∈ S, a ≤ N) →
    wsum (N + 1) S = wsum N S + wsum N S := by
  intro S
  induction S with
  | nil => intro N _; rfl
  | cons a S' ih =>
    intro N hS
    have ha : a ≤ N := hS a (List.mem_cons_self)
    have hrest : ∀ x ∈ S', x ≤ N := fun x hx => hS x (List.mem_cons_of_mem a hx)
    have ih' := ih N hrest
    have he : N + 1 - a = (N - a) + 1 := by omega
    have hp : 2 ^ (N + 1 - a) = 2^(N - a) + 2^(N - a) := by
      rw [he, Nat.pow_succ]
      omega
    simp only [wsum_cons, wsum_cons]
    rw [hp, Nat.mul_add]
    omega

/-- Arithmetic step: one more exponent doubles the target value. -/
theorem target_step (n k : Nat) : n * 2^(k + 1) = n * 2^k + n * 2^k := by
  rw [Nat.pow_succ]
  have h : 2^k * 2 = 2^k + 2^k := by omega
  rw [h, Nat.mul_add]

/-- THE GREEDY WALK.  Fields (n, N, v, S):
    n = the Erdős index, (N, v) = walk state, S = taken indices (reversed). -/
inductive Walk : Nat → Nat → Nat → List Nat → Prop
  | start1 : Walk 1 3 2 []
  | startn (n : Nat) (hn : 2 ≤ n) : Walk n (n + 1) n []
  | take {n N v : Nat} {S : List Nat} (hN : N ≤ 2 * v) (hw : Walk n N v S) :
      Walk n (N + 1) (2 * v - N) (N :: S)
  | skip {n N v : Nat} {S : List Nat} (hN : 2 * v < N) (hw : Walk n N v S) :
      Walk n (N + 1) (2 * v) S

/-- Full walk invariant, by induction on the derivation:
    (1) v + v + wsum N S = n * 2^(N − n)   (the scaling identity)
    (2) every taken index < N
    (3) n ≤ N. -/
theorem walk_invariant {n N v : Nat} {S : List Nat} (hw : Walk n N v S) :
    v + v + wsum N S = n * 2^(N - n) ∧ (∀ a ∈ S, a < N) ∧ n ≤ N := by
  induction hw with
  | start1 =>
    refine ⟨?_, ?_, ?_⟩
    · show 2 + 2 + wsum 3 [] = 1 * 2^(3 - 1)
      decide
    · intro a ha; cases ha
    · decide
  | startn n hn =>
    refine ⟨?_, ?_, ?_⟩
    · show n + n + wsum (n + 1) [] = n * 2^(n + 1 - n)
      rw [wsum_nil, Nat.add_sub_cancel_left, Nat.pow_one]
      omega
    · intro a ha; cases ha
    · omega
  | @take n N v S hN hw ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hlt : ∀ a ∈ S, a ≤ N :=
      fun a ha => Nat.le_of_lt (ih2 a ha)
    have hshift := wsum_shift S N hlt
    refine ⟨?_, ?_, ?_⟩
    · show (2 * v - N) + (2 * v - N) + wsum (N + 1) (N :: S) = n * 2^(N + 1 - n)
      have he : N + 1 - n = (N - n) + 1 := by omega
      rw [he, target_step]
      have hhead : wsum (N + 1) (N :: S) = (N + N) + (wsum N S + wsum N S) := by
        simp only [wsum_cons]
        have he2 : N + 1 - N = 1 := by omega
        rw [he2, Nat.pow_one, hshift]
        omega
      rw [hhead]
      omega
    · intro a ha
      cases ha with
      | head => omega
      | tail _ ha' => exact Nat.lt_succ_of_lt (ih2 a ha')
    · omega
  | @skip n N v S hN hw ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hlt : ∀ a ∈ S, a ≤ N :=
      fun a ha => Nat.le_of_lt (ih2 a ha)
    have hshift := wsum_shift S N hlt
    refine ⟨?_, ?_, ?_⟩
    · show (2 * v) + (2 * v) + wsum (N + 1) S = n * 2^(N + 1 - n)
      have he : N + 1 - n = (N - n) + 1 := by omega
      rw [he, target_step, hshift]
      omega
    · intro a ha; exact Nat.lt_succ_of_lt (ih2 a ha)
    · omega

/-- MAIN THEOREM — the certificate identity.  A terminating greedy walk
    from n yields the exact integer identity
        Σ_{a ∈ S} a * 2^(N − a) = n * 2^(N − n),
    which after division by 2^N (DERIVATION.md) is precisely the
    Erdős #261 representation  n/2^n = Σ_{a∈S} a/2^a. -/
theorem walk_zero_identity {n N : Nat} {S : List Nat} (hw : Walk n N 0 S) :
    wsum N S = n * 2^(N - n) := by
  have h := (walk_invariant hw).1
  omega

/-- A walk state with S = [] occurs only at the two start configurations. -/
theorem walk_nil_char : ∀ {n N v : Nat} {S : List Nat}, Walk n N v S → S = [] →
    (n = 1 ∧ N = 3 ∧ v = 2) ∨ (N = n + 1 ∧ v = n ∧ 2 ≤ n) := by
  intro n N v S hw
  induction hw with
  | start1 => intro hS; left; exact ⟨rfl, rfl, rfl⟩
  | startn n hn => intro hS; right; exact ⟨rfl, rfl, hn⟩
  | @take n N v S hN hw ih =>
    intro hS
    simp at hS
  | @skip n N v S hN hw ih =>
    intro hS
    obtain hch | hch := ih hS
    · obtain ⟨h1, h2, h3⟩ := hch; omega
    · obtain ⟨h2, h3, hn⟩ := hch; omega

/-- Every terminating walk from n ≥ 2 produces a genuine multi-term
    witness: |S| ≥ 2 (the t ≥ 2 requirement of Erdős #261). -/
theorem walk_zero_two_pieces : ∀ {n N v : Nat} {S : List Nat}, Walk n N v S → v = 0 →
    2 ≤ n → 2 ≤ S.length := by
  intro n N v S hw
  induction hw with
  | start1 => intro hv hn; omega
  | startn n hn' => intro hv hn; omega
  | @take n N v S hN hw ih =>
    intro hzero hn
    cases S with
    | nil =>
      exfalso
      obtain hch | hch := walk_nil_char hw rfl
      · obtain ⟨h1, _, _⟩ := hch; omega
      · obtain ⟨rfl, rfl, _⟩ := hch; omega
    | cons a S' =>
      simp only [List.length_cons]
      omega
  | @skip n N v S hN hw ih =>
    intro hzero hn
    have hv0 : v = 0 := by omega
    exact ih hv0 hn

/-! ### Concrete kernel-checked witnesses (from the computational scan) -/

/-- Certificate checker: exact integer verification of a witness list. -/
def checkWit (n : Nat) (S : List Nat) : Bool :=
  let M := S.foldr Nat.max 0
  wsum M S == n * 2^(M - n)

-- n = 3: witness {4, 6, 8}:  3/8 = 4/16 + 6/64 + 8/256
example : checkWit 3 [4, 6, 8] = true := by decide

-- n = 4: Borwein–Loring:  4/16 = 5/32 + 6/64
example : checkWit 4 [5, 6] = true := by decide

-- n = 5: witness {6, 7, 11, 13, 14}
example : checkWit 5 [6, 7, 11, 13, 14] = true := by decide

-- n = 8 (first census-resistant case; witness needs offsets up to 32)
example : checkWit 8 [9, 10, 12, 14, 18, 19, 21, 22, 24, 26, 29, 30, 32] = true := by
  decide

-- Walk-derivation instances: the n = 4 and n = 3 witnesses ARE walk products.
-- n = 4: (5,4) → take 5 → (6,3) → take 6 → (7,0), S = [6,5]
example : Walk 4 7 0 [6, 5] :=
  Walk.take (n := 4) (N := 6) (v := 3) (S := [5]) (by decide)
    (Walk.take (n := 4) (N := 5) (v := 4) (S := []) (by decide)
      (Walk.startn 4 (by decide)))

-- n = 3: (4,3) → take 4 → (5,2) → skip → (6,4) → take 6 → (7,2) → skip
--        → (8,4) → take 8 → (9,0), S = [8,6,4]
example : Walk 3 9 0 [8, 6, 4] :=
  Walk.take (n := 3) (N := 8) (v := 4) (S := [6, 4]) (by decide)
    (Walk.skip (n := 3) (N := 7) (v := 2) (S := [6, 4]) (by decide)
      (Walk.take (n := 3) (N := 6) (v := 4) (S := [4]) (by decide)
        (Walk.skip (n := 3) (N := 5) (v := 2) (S := [4]) (by decide)
          (Walk.take (n := 3) (N := 4) (v := 3) (S := []) (by decide)
            (Walk.startn 3 (by decide))))))

#print axioms walk_zero_identity
#print axioms walk_zero_two_pieces
