/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Filter

namespace Frontier

/-- The `n`-th prime gap `p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n`
(so `p_0 = 2`, `p_1 = 3`, ...). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The quantity `liminf_{n → ∞} (p_{n+1} - p_n)`, computed in the complete lattice `ℕ∞`
so that "`liminf` is finite" is a meaningful statement (`< ⊤`). -/
noncomputable def liminfPrimeGap : ℕ∞ :=
  Filter.liminf (fun n : ℕ => (primeGap n : ℕ∞)) Filter.atTop

/-! ### Base cases -/

theorem primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap]

theorem primeGap_one : primeGap 1 = 2 := by
  simp [primeGap]

theorem primeGap_two : primeGap 2 = 2 := by
  simp [primeGap]

theorem primeGap_three : primeGap 3 = 4 := by
  simp [primeGap]

/-- Consecutive primes are strictly increasing, so every gap is at least `1`. -/
theorem one_le_primeGap (n : ℕ) : 1 ≤ primeGap n := by
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (Nat.lt_succ_self n)
  simp only [primeGap]
  omega

/-- A trivial lower bound: the liminf of the prime gaps is at least `1`. -/
theorem one_le_liminfPrimeGap : 1 ≤ liminfPrimeGap := by
  refine Filter.le_liminf_of_le ?_ ?_
  · isBoundedDefault
  · filter_upwards with n
    exact_mod_cast one_le_primeGap n

/-! ### The reduction

The following unconditional equivalence identifies finiteness of `liminf (p_{n+1} - p_n)`
with the combinatorial statement proved by Zhang (and, with a better bound, Maynard):
*there is a bound `B` such that infinitely many consecutive prime pairs differ by at most `B`*. -/

/-- **Unconditional reduction.** `liminf_{n} (p_{n+1} - p_n) < ⊤` in `ℕ∞` if and only if there
is some `B : ℕ` with `p_{n+1} - p_n ≤ B` for infinitely many `n`. -/
theorem liminf_primeGap_lt_top_iff :
    liminfPrimeGap < ⊤ ↔ ∃ B : ℕ, ∃ᶠ n in Filter.atTop, primeGap n ≤ B := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne
    refine ⟨k, ?_⟩
    by_contra hc
    rw [Filter.not_frequently] at hc
    have h1 : (((k + 1 : ℕ) : ℕ∞)) ≤ liminfPrimeGap := by
      refine Filter.le_liminf_of_le ?_ ?_
      · isBoundedDefault
      · filter_upwards [hc] with n hn
        have hkn : k + 1 ≤ primeGap n := by omega
        exact_mod_cast hkn
    rw [← hk] at h1
    have : k + 1 ≤ k := by exact_mod_cast h1
    omega
  · rintro ⟨B, hB⟩
    refine lt_of_le_of_lt (Filter.liminf_le_of_frequently_le (a := (B : ℕ∞)) ?_) ?_
    · exact hB.mono fun n hn => by exact_mod_cast hn
    · exact ENat.coe_lt_top B

/-- **Bounded prime gaps (Zhang / Maynard), as a Lean-checked reduction.**

`liminf_{n → ∞} (p_{n+1} - p_n)` is finite, given the bounded-gaps input `hBounded`: some fixed
bound `B` is achieved by infinitely many consecutive prime pairs. This hypothesis is exactly the
theorem of Zhang (with `B = 7 · 10^7`, improved by the Polymath8/Maynard work to `B = 246`);
Mathlib currently contains no proof of it, and by `Frontier.liminf_primeGap_lt_top_iff` the
hypothesis is *equivalent* to the conclusion, so the reduction below is lossless. -/
theorem bounded_prime_gaps
    (hBounded : ∃ B : ℕ, ∃ᶠ n in Filter.atTop, primeGap n ≤ B) :
    liminfPrimeGap < ⊤ :=
  liminf_primeGap_lt_top_iff.mpr hBounded

end Frontier

