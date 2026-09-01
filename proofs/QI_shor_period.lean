import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- The modular exponentiation function `k ↦ a ^ k mod n`, the function whose period
Shor's algorithm computes. -/
def modExp (n a k : ℕ) : ZMod n := (a : ZMod n) ^ k

/-- If `a` is coprime to `n` then `a` has finite multiplicative order in `ZMod n`. -/
lemma isOfFinOrder_coprime {n a : ℕ} (hn : 0 < n) (h : Nat.Coprime a n) :
    IsOfFinOrder (a : ZMod n) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨Nat.totient n, Nat.totient_pos.mpr hn, ?_⟩
  have h1 : ((a ^ Nat.totient n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient h)
  simpa using h1

/-- The order of `a` in `ZMod n` is a period of `k ↦ a ^ k`. -/
lemma modExp_add_order (n a k : ℕ) :
    modExp n a (k + orderOf (a : ZMod n)) = modExp n a k := by
  simp [modExp, pow_add, pow_orderOf_eq_one]

/-- Minimality: no positive number smaller than the order is a period. -/
lemma modExp_ne_of_lt_order {n a p : ℕ} (hp : 0 < p) (hlt : p < orderOf (a : ZMod n)) :
    modExp n a p ≠ modExp n a 0 := by
  intro hcon
  simp only [modExp, pow_zero] at hcon
  exact (pow_ne_one_of_lt_orderOf hp.ne' hlt) hcon

/-- Exact characterization of the periods of `k ↦ a ^ k mod n`: they are the multiples
of the order. -/
lemma modExp_period_iff (n a p : ℕ) :
    (∀ k, modExp n a (k + p) = modExp n a k) ↔ orderOf (a : ZMod n) ∣ p := by
  constructor
  · intro hper
    have h0 := hper 0
    simp only [modExp, zero_add, pow_zero] at h0
    exact orderOf_dvd_of_pow_eq_one h0
  · rintro ⟨c, rfl⟩ k
    simp [modExp, pow_add, pow_mul, pow_orderOf_eq_one]

/-- Continued-fraction recovery step: from an exact rational `s / r` with `s` coprime to
the period `r`, the denominator recovered in lowest terms is exactly `r`. -/
lemma den_eq_of_coprime {s r : ℕ} (hr : 0 < r) (h : Nat.Coprime s r) :
    ((s : ℚ) / (r : ℚ)).den = r := by
  have h1 := Rat.den_div_eq_of_coprime (a := (s : ℤ)) (b := (r : ℤ)) (by exact_mod_cast hr)
    (by simpa using h)
  push_cast at h1
  exact_mod_cast h1

/-- The number of "good" measurement outcomes `s ∈ {0, …, r-1}` (those coprime to the
period `r`, i.e. those from which the period is recovered exactly) is `φ r`. -/
lemma card_good_outcomes (r : ℕ) :
    ((Finset.range r).filter (fun s => Nat.Coprime s r)).card = Nat.totient r := by
  rw [Nat.totient]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [Nat.coprime_comm]

/-- Amplification: repeating a procedure that succeeds with probability `p > 0`
independently `t` times makes the failure probability `(1 - p) ^ t` arbitrarily small. -/
lemma failure_prob_lt {p : ℝ} (hp : 0 < p) {eps : ℝ} (heps : 0 < eps) :
    ∃ t : ℕ, (1 - p) ^ t < eps :=
  exists_pow_lt_of_lt_one heps (by linarith)

/--
**Shor's period finding.**

Let `n > 1` and let `a` be coprime to `n`, and let `r` be the order of `a` modulo `n`.
Then:

1. `r > 0` and `r` is a period of the modular exponentiation function `k ↦ a ^ k mod n`;
2. `r` is the *minimal* period, and in fact the periods are exactly the multiples of `r`;
3. (recovery) a measurement outcome giving the exact rational `s / r` with `s` coprime to
   `r` determines `r`: the denominator of `s / r` in lowest terms is `r`.  This is the
   continued-fraction post-processing step of Shor's algorithm;
4. (with high probability) the number of good outcomes `s < r` is `φ r`, so a single run
   succeeds with probability `φ r / r > 0`, and hence for any `ε > 0` there is a number of
   independent repetitions `t` after which the failure probability `(1 - φ r / r) ^ t` is
   below `ε`; i.e. the period is recovered with probability arbitrarily close to `1`.
-/
theorem shor_period {n a : ℕ} (hn : 1 < n) (hcop : Nat.Coprime a n)
    (r : ℕ) (hr : r = orderOf (a : ZMod n)) :
    0 < r
    ∧ (∀ k, modExp n a (k + r) = modExp n a k)
    ∧ (∀ p, 0 < p → p < r → modExp n a p ≠ modExp n a 0)
    ∧ (∀ p, (∀ k, modExp n a (k + p) = modExp n a k) ↔ r ∣ p)
    ∧ (∀ s : ℕ, Nat.Coprime s r → ((s : ℚ) / (r : ℚ)).den = r)
    ∧ ((Finset.range r).filter (fun s => Nat.Coprime s r)).card = Nat.totient r
    ∧ 0 < (Nat.totient r : ℝ) / r
    ∧ (∀ eps : ℝ, 0 < eps → ∃ t : ℕ, (1 - (Nat.totient r : ℝ) / r) ^ t < eps) := by
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  subst hr
  have hfin : IsOfFinOrder (a : ZMod n) := isOfFinOrder_coprime hn0 hcop
  have hrpos : 0 < orderOf (a : ZMod n) := hfin.orderOf_pos
  set r := orderOf (a : ZMod n) with hrdef
  have htot : 0 < (Nat.totient r : ℝ) / r := by
    apply div_pos
    · exact_mod_cast Nat.totient_pos.mpr hrpos
    · exact_mod_cast hrpos
  exact ⟨hrpos, modExp_add_order n a, fun p hp hlt => modExp_ne_of_lt_order hp hlt,
    modExp_period_iff n a, fun s hs => den_eq_of_coprime hrpos hs,
    card_good_outcomes r, htot, fun eps heps => failure_prob_lt htot heps⟩

end QI

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

