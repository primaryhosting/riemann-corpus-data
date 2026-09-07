import Mathlib

/-!
# Partial results toward the Collatz (3n+1) conjecture

The **Collatz conjecture** — that every positive integer eventually reaches `1`
under the map `n ↦ n/2` (n even) / `n ↦ 3n+1` (n odd) — is **OPEN**. Nothing in
this file resolves it. The full statement is recorded as an unproven `def`
(`CollatzConjecture`), never as a theorem.

What *is* proved here are genuine, unconditional partial results:

* the base case and the trivial cycle `1 → 4 → 2 → 1`;
* every power of two reaches `1` (`reaches1_pow_two`);
* reaching `1` is preserved under multiplication by a power of two
  (`reaches1_two_mul`, `reaches1_mul_pow_two`);
* a Terras-style one-step descent for `n ≡ 1 (mod 4)`: such an `n > 1` drops
  below itself after exactly three Collatz steps (`descent_mod4_one`).

All proofs are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace Brockian.CollatzPartial

/-- One Collatz step: halve if even, else `3n+1`. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` reaches `1` under iteration of `collatz`. -/
def Reaches1 (n : ℕ) : Prop := ∃ k : ℕ, collatz^[k] n = 1

/-- The Collatz conjecture (**OPEN**). Recorded as an unproven `def`, never a
theorem: every positive integer eventually reaches `1`. -/
def CollatzConjecture : Prop := ∀ n : ℕ, 0 < n → Reaches1 n

/-! ## (1) Base case and the trivial cycle -/

/-- `1` reaches `1` in zero steps. -/
theorem reaches1_one : Reaches1 1 := ⟨0, rfl⟩

theorem collatz_one : collatz 1 = 4 := by decide

theorem collatz_four : collatz 4 = 2 := by decide

theorem collatz_two : collatz 2 = 1 := by decide

/-- The trivial Collatz cycle `1 → 4 → 2 → 1`. -/
theorem trivial_cycle : collatz^[3] 1 = 1 := by decide

/-! ## (2) Powers of two reach `1` -/

/-- A Collatz step on an even number `2n` halves it to `n`. -/
theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  unfold collatz
  split <;> omega

/-- **Flagship partial result.** Every power of two reaches `1`:
`2^k → 2^(k-1) → … → 2 → 1`, i.e. `collatz^[k] (2^k) = 1`. -/
theorem reaches1_pow_two (k : ℕ) : Reaches1 (2 ^ k) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨j + 1, ?_⟩
      have hstep : collatz (2 ^ (m + 1)) = 2 ^ m := by
        rw [pow_succ, Nat.mul_comm (2 ^ m) 2]
        exact collatz_two_mul (2 ^ m)
      rw [Function.iterate_succ_apply, hstep]
      exact hj

/-! ## (3) Descent by halving -/

/-- If a positive `n` reaches `1`, so does `2n` (one extra halving step). -/
theorem reaches1_two_mul {n : ℕ} (hn : 0 < n) (h : Reaches1 n) : Reaches1 (2 * n) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [Function.iterate_succ_apply, collatz_two_mul]
  exact hk

/-- If a positive `n` reaches `1`, so does `2^k * n` for every `k`. -/
theorem reaches1_mul_pow_two {n : ℕ} (hn : 0 < n) (h : Reaches1 n) (k : ℕ) :
    Reaches1 (2 ^ k * n) := by
  induction k with
  | zero => simpa using h
  | succ m ih =>
      have hpos : 0 < 2 ^ m * n :=
        Nat.mul_pos (pow_pos (show (0 : ℕ) < 2 by norm_num) m) hn
      have hrw : 2 ^ (m + 1) * n = 2 * (2 ^ m * n) := by ring
      rw [hrw]
      exact reaches1_two_mul hpos ih

/-! ## (4) Terras-style descent for `n ≡ 1 (mod 4)`

Every `n ≡ 1 (mod 4)` with `n > 1` strictly decreases after finitely many
Collatz steps. Concretely, writing `n = 4m+1` (with `m ≥ 1`):

* `n` is odd, so `collatz n = 3n+1 = 12m+4` (even);
* `collatz (12m+4) = 6m+2` (even);
* `collatz (6m+2) = 3m+1 < 4m+1 = n`.

So `k = 3` steps already send `n` below itself. This is a genuine unconditional
descent lemma — one of the classical ingredients in the average-case theory of
Collatz — but it does **not** resolve the conjecture. -/
theorem descent_mod4_one {n : ℕ} (h1 : 1 < n) (h : n % 4 = 1) :
    ∃ k, 0 < k ∧ collatz^[k] n < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  have hm : 1 ≤ m := by omega
  refine ⟨3, by norm_num, ?_⟩
  -- The three explicit Collatz steps.
  have s1 : collatz (4 * m + 1) = 12 * m + 4 := by unfold collatz; split <;> omega
  have s2 : collatz (12 * m + 4) = 6 * m + 2 := by unfold collatz; split <;> omega
  have s3 : collatz (6 * m + 2) = 3 * m + 1 := by unfold collatz; split <;> omega
  have hval : collatz^[3] (4 * m + 1) = 3 * m + 1 := by
    show collatz (collatz (collatz (4 * m + 1))) = 3 * m + 1
    rw [s1, s2, s3]
  rw [hval]
  omega

end Brockian.CollatzPartial
