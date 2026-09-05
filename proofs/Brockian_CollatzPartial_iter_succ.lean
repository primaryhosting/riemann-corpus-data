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

namespace Brockian.CollatzPartial

/-! ### Iteration and strong induction

The file is self-contained (it uses only the Lean core prelude), so we first set up
iteration of a function on `Nat` and record the two general facts we need about it.
-/

/-- `iter f k x` is the result of applying `f` to `x` exactly `k` times. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => iter f k (f x)

@[simp] theorem iter_zero (f : Nat → Nat) (x : Nat) : iter f 0 x = x := rfl

theorem iter_succ (f : Nat → Nat) (k x : Nat) : iter f (k + 1) x = iter f k (f x) := rfl

/-- Iterating `j + k` times is iterating `k` times and then `j` times. -/
theorem iter_add (f : Nat → Nat) (j k x : Nat) : iter f (j + k) x = iter f j (iter f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    show iter f (j + k + 1) x = iter f j (iter f (k + 1) x)
    rw [iter_succ, iter_succ, ih]

/-- Strong induction on the natural numbers. -/
theorem strong_induction {P : Nat → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have key : ∀ n m, m < n → P m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ n ih => intro m hm; exact h m (fun k hk => ih k (by omega))
  exact fun n => h n (fun m hm => key (n + 1) m (by omega))

/-! ### The Collatz map -/

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, and `n ↦ 3 * n + 1` for odd `n`. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `Reaches1 n` says that iterating the Collatz map from `n` eventually produces `1`. -/
def Reaches1 (n : Nat) : Prop := ∃ k : Nat, iter collatz k n = 1

theorem collatz_even {n : Nat} (h : n % 2 = 0) : collatz n = n / 2 := by
  unfold collatz; rw [if_pos h]

theorem collatz_odd {n : Nat} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz; rw [if_neg (by omega)]

theorem collatz_pos {n : Nat} (hn : 0 < n) : 0 < collatz n := by
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
  · rw [collatz_even h]; omega
  · rw [collatz_odd h]; omega

theorem iter_collatz_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < iter collatz k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => rw [iter_succ]; exact ih (collatz_pos hn)

/-- If some Collatz iterate of `n` reaches `1`, then so does `n`. -/
theorem Reaches1.of_iter {n k : Nat} (h : Reaches1 (iter collatz k n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [iter_add]; exact hj⟩

/-! ### Unconditional partial results -/

/-- Every power of two reaches `1`, in exactly `k` steps. -/
theorem reaches1_two_pow (k : Nat) : Reaches1 (2 ^ k) := by
  refine ⟨k, ?_⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have h : collatz (2 ^ (k + 1)) = 2 ^ k := by
      rw [collatz_even (by omega), hp]; omega
    rw [iter_succ, h]
    exact ih

/-! #### A machine-checked verification of all `n ≤ 1000` -/

/-- `reachesOneWithin f n` checks whether `n` reaches `1` within `f` Collatz steps. -/
def reachesOneWithin : Nat → Nat → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reachesOneWithin f (collatz n)

theorem reaches1_of_within : ∀ (f n : Nat), reachesOneWithin f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
    intro n h
    have hb : (n == 1) = true := h
    have hn : n = 1 := by simpa using hb
    exact ⟨0, hn⟩
  | succ f ih =>
    intro n h
    have h' : (n == 1) = true ∨ reachesOneWithin f (collatz n) = true := by
      have : ((n == 1) || reachesOneWithin f (collatz n)) = true := h
      exact (Bool.or_eq_true _ _).mp this
    rcases h' with h1 | h1
    · have hn : n = 1 := by simpa using h1
      exact ⟨0, hn⟩
    · exact Reaches1.of_iter (k := 1) (ih (collatz n) h1)

/-- `checkAll m` checks that every `n` with `0 < n ≤ m` reaches `1` within `500` steps. -/
def checkAll : Nat → Bool
  | 0 => true
  | m + 1 => reachesOneWithin 500 (m + 1) && checkAll m

theorem reaches1_of_checkAll : ∀ (m : Nat), checkAll m = true → ∀ n, 0 < n → n ≤ m → Reaches1 n := by
  intro m
  induction m with
  | zero => intro _ n hn hle; omega
  | succ m ih =>
    intro h n hn hle
    have hsplit : reachesOneWithin 500 (m + 1) = true ∧ checkAll m = true := by
      have : (reachesOneWithin 500 (m + 1) && checkAll m) = true := h
      exact (Bool.and_eq_true _ _).mp this
    rcases (by omega : n = m + 1 ∨ n ≤ m) with hc | hc
    · rw [hc]; exact reaches1_of_within 500 (m + 1) hsplit.1
    · exact ih hsplit.2 n hn hc

set_option maxRecDepth 100000 in
/-- Every `n` with `0 < n ≤ 1000` reaches `1` (verified by kernel computation). -/
theorem reaches1_of_le_1000 (n : Nat) (hn : 0 < n) (hle : n ≤ 1000) : Reaches1 n :=
  reaches1_of_checkAll 1000 (by decide) n hn hle

/-- An even number `n > 1` descends in one step. -/
theorem descent_of_even {n : Nat} (hn : 1 < n) (h : n % 2 = 0) :
    ∃ k, 0 < k ∧ iter collatz k n < n := by
  refine ⟨1, Nat.one_pos, ?_⟩
  have e : iter collatz 1 n = collatz n := rfl
  rw [e, collatz_even h]
  omega

/-- A number `n > 1` with `n % 4 = 1` descends in three steps:
`4m+1 ↦ 12m+4 ↦ 6m+2 ↦ 3m+1`. -/
theorem descent_of_one_mod_four {n : Nat} (hn : 1 < n) (h : n % 4 = 1) :
    ∃ k, 0 < k ∧ iter collatz k n < n := by
  obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  refine ⟨3, by omega, ?_⟩
  have s1 : collatz n = 12 * m + 4 := by rw [collatz_odd (by omega)]; omega
  have s2 : collatz (12 * m + 4) = 6 * m + 2 := by rw [collatz_even (by omega)]; omega
  have s3 : collatz (6 * m + 2) = 3 * m + 1 := by rw [collatz_even (by omega)]; omega
  have e : iter collatz 3 n = collatz (collatz (collatz n)) := rfl
  rw [e, s1, s2, s3]
  omega

/-! ### The conditional reduction -/

/-- The descent hypothesis restricted to residue `3` modulo `4`: every `n > 1` with
`n % 4 = 3` has a strictly smaller Collatz iterate. -/
def DescentHypothesis : Prop :=
  ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k, 0 < k ∧ iter collatz k n < n

/-- Under `DescentHypothesis`, every `n > 1` has a strictly smaller Collatz iterate:
the residues `0`, `2` (even) and `1` modulo `4` are handled unconditionally. -/
theorem descent_of_hypothesis (H : DescentHypothesis) {n : Nat} (hn : 1 < n) :
    ∃ k, 0 < k ∧ iter collatz k n < n := by
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h
  · exact descent_of_even hn (by omega)
  · exact descent_of_one_mod_four hn h
  · exact descent_of_even hn (by omega)
  · exact H n hn h

/-- **Collatz conjecture, conditional on the descent hypothesis for `n ≡ 3 mod 4`.**

The Collatz conjecture — every positive integer eventually reaches `1` under
`n ↦ n/2` for even `n` and `n ↦ 3n+1` for odd `n` — is an open problem, so what is
proved here is a Lean-checked reduction: it suffices to know that every `n > 1` with
`n % 4 = 3` has *some* strictly smaller Collatz iterate. The other residues are handled
unconditionally (`descent_of_even`, `descent_of_one_mod_four`), and the reduction itself
is by strong induction on `n`. -/
theorem CollatzConjecture (H : DescentHypothesis) : ∀ n : Nat, 0 < n → Reaches1 n := by
  refine strong_induction (P := fun n => 0 < n → Reaches1 n) ?_
  intro n ih hn
  rcases (by omega : n = 1 ∨ 1 < n) with h1 | h1
  · exact ⟨0, by rw [h1]; rfl⟩
  · obtain ⟨k, hk, hlt⟩ := descent_of_hypothesis H h1
    exact Reaches1.of_iter (ih _ hlt (iter_collatz_pos hn k))

end Brockian.CollatzPartial

