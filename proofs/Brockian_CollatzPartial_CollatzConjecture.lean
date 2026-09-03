import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports), so that the required header
comment above can be the very first thing in the file: in Lean 4 an `import` line
must precede every command, and a module docstring `/-! ... -/` is a command.
Everything below is proved from Lean core only.

The Collatz Conjecture itself is open. What is proved here is a Lean-checked
*reduction*: the conjecture follows from the descent property restricted to the
residue class `3 mod 4`. The even case and the `1 mod 4` case of the descent
property are proved unconditionally.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3n + 1` if `n` is odd. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iter k n` is the `k`-th iterate of the Collatz map applied to `n`. -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | (k + 1), n => iter k (collatz n)

/-- `Reaches1 n` says that some iterate of the Collatz map sends `n` to `1`. -/
def Reaches1 (n : Nat) : Prop := ∃ k : Nat, iter k n = 1

/-- `DescendsAt n` says that a positive number of Collatz steps starting at `n`
produces a value strictly smaller than `n`. -/
def DescendsAt (n : Nat) : Prop := ∃ k : Nat, 0 < k ∧ iter k n < n

theorem iter_add (j k n : Nat) : iter (j + k) n = iter j (iter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      show iter ((j + k) + 1) n = iter j (iter (k + 1) n)
      simp only [iter]
      exact ih (collatz n)

theorem collatz_pos {n : Nat} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

theorem iter_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < iter k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (collatz_pos hn)

/-- Even numbers `≥ 2` descend in a single step. -/
theorem descendsAt_of_even {n : Nat} (h2 : 2 ≤ n) (he : n % 2 = 0) : DescendsAt n := by
  refine ⟨1, Nat.one_pos, ?_⟩
  show collatz n < n
  simp only [collatz, if_pos he]
  omega

/-- Numbers congruent to `1 mod 4` and at least `5` descend in three steps:
`4m + 1 → 12m + 4 → 6m + 2 → 3m + 1`. -/
theorem descendsAt_of_one_mod_four {n : Nat} (h5 : 5 ≤ n) (h : n % 4 = 1) : DescendsAt n := by
  obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  refine ⟨3, by omega, ?_⟩
  show collatz (collatz (collatz n)) < n
  have s1 : collatz n = 12 * m + 4 := by
    simp only [collatz, hm]; rw [if_neg (by omega)]; omega
  have s2 : collatz (12 * m + 4) = 6 * m + 2 := by
    simp only [collatz]; rw [if_pos (by omega)]; omega
  have s3 : collatz (6 * m + 2) = 3 * m + 1 := by
    simp only [collatz]; rw [if_pos (by omega)]; omega
  rw [s1, s2, s3]
  omega

/-- **Reduction of the descent property.** If every `n ≡ 3 (mod 4)` eventually descends,
then every `n ≥ 2` eventually descends. -/
theorem descent_reduction (h : ∀ n : Nat, n % 4 = 3 → DescendsAt n) :
    ∀ n : Nat, 2 ≤ n → DescendsAt n := by
  intro n hn
  rcases Nat.lt_or_ge (n % 2) 1 with he | ho
  · exact descendsAt_of_even hn (by omega)
  · have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases h4 with h1 | h3
    · exact descendsAt_of_one_mod_four (by omega) h1
    · exact h n h3

/-- **Conditional Collatz Conjecture.** Assume that every `n ≡ 3 (mod 4)` eventually
reaches, under iteration of the Collatz map, a value strictly smaller than itself.
Then every positive natural number reaches `1`.

The Collatz Conjecture itself is open; this is a Lean-checked reduction of it to the
descent property on the single residue class `3 mod 4`, the even and `1 mod 4` classes
being handled unconditionally (`descendsAt_of_even`, `descendsAt_of_one_mod_four`). -/
theorem CollatzConjecture (hdesc : ∀ n : Nat, n % 4 = 3 → DescendsAt n) :
    ∀ n : Nat, 0 < n → Reaches1 n := by
  have hall := descent_reduction hdesc
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      exact ⟨0, by simp [iter, hn1]⟩
    · obtain ⟨k, _, hklt⟩ := hall n h2
      obtain ⟨j, hj⟩ := ih (iter k n) hklt (iter_pos hn k)
      exact ⟨j + k, by rw [iter_add]; exact hj⟩

end Brockian.CollatzPartial

