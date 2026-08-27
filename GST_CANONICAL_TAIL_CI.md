# GST Canonical Tail Projection CI

Commit: 56352292a85c6e44a606f24ffe3ce5b3ed3da609

lake build GSTCanonicalTailSupport exit: 1

```text
✖ [8697/8698] Building GSTMathlibProbe (3.8s)
trace: .> LEAN_PATH=/home/runner/work/erdosternary2/erdosternary2/.lake/packages/Cli/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/batteries/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/Qq/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/aesop/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/importGraph/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/plausible/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/packages/mathlib/.lake/build/lib/lean:/home/runner/work/erdosternary2/erdosternary2/.lake/build/lib/lean /home/runner/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean /home/runner/work/erdosternary2/erdosternary2/GSTMathlibProbe.lean -o /home/runner/work/erdosternary2/erdosternary2/.lake/build/lib/lean/GSTMathlibProbe.olean -i /home/runner/work/erdosternary2/erdosternary2/.lake/build/lib/lean/GSTMathlibProbe.ilean -c /home/runner/work/erdosternary2/erdosternary2/.lake/build/ir/GSTMathlibProbe.c --setup /home/runner/work/erdosternary2/erdosternary2/.lake/build/ir/GSTMathlibProbe.setup.json --json
info: GSTMathlibProbe.lean:3:0: Nat.mod_add_div (m k : ℕ) : m % k + k * (m / k) = m
info: GSTMathlibProbe.lean:4:0: Nat.div_add_mod (m n : ℕ) : n * (m / n) + m % n = m
info: GSTMathlibProbe.lean:5:0: Nat.add_mul_mod_self_left (x y z : ℕ) : (x + y * z) % y = x % y
info: GSTMathlibProbe.lean:6:0: Nat.add_mul_mod_self_right (x y z : ℕ) : (x + y * z) % z = x % z
info: GSTMathlibProbe.lean:7:0: Nat.mul_add_mod_self_left (a b c : ℕ) : (a * b + c) % a = c % a
info: GSTMathlibProbe.lean:8:0: Nat.mul_add_mod_self_right (a b c : ℕ) : (a * b + c) % b = c % b
info: GSTMathlibProbe.lean:9:0: Nat.add_mul_div_left (x z : ℕ) {y : ℕ} (H : 0 < y) : (x + y * z) / y = x / y + z
info: GSTMathlibProbe.lean:10:0: Nat.add_mul_div_right (x y : ℕ) {z : ℕ} (H : 0 < z) : (x + y * z) / z = x / z + y
info: GSTMathlibProbe.lean:11:0: Nat.mul_add_div {m : ℕ} (m_pos : m > 0) (x y : ℕ) : (m * x + y) / m = x + y / m
error: GSTMathlibProbe.lean:12:7: Unknown constant `Nat.mul_add_div_left`
error: GSTMathlibProbe.lean:13:7: Unknown constant `Nat.div_add`
info: GSTMathlibProbe.lean:14:0: Nat.add_div {a b c : ℕ} (h : 0 < c) : (a + b) / c = a / c + b / c + if c ≤ a % c + b % c then 1 else 0
info: GSTMathlibProbe.lean:15:0: Nat.div_eq_of_lt {a b : ℕ} (h₀ : a < b) : a / b = 0
info: GSTMathlibProbe.lean:16:0: Nat.mod_eq_of_lt {a b : ℕ} (h : a < b) : a % b = a
error: GSTMathlibProbe.lean:17:7: Unknown constant `Nat.div_mul_eq_div_div`
info: GSTMathlibProbe.lean:18:0: Nat.div_div_eq_div_mul (m n k : ℕ) : m / n / k = m / (n * k)
info: GSTMathlibProbe.lean:19:0: Nat.mul_mod (a b n : ℕ) : a * b % n = a % n * (b % n) % n
info: GSTMathlibProbe.lean:20:0: Nat.add_mod (a b n : ℕ) : (a + b) % n = (a % n + b % n) % n
error: Lean exited with code 1
Some required targets logged failures:
- GSTMathlibProbe
error: build failed
```
