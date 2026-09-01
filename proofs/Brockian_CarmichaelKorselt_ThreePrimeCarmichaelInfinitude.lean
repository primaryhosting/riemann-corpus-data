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

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` which is a Fermat pseudoprime to every base,
i.e. `a ^ n ≡ a [MOD n]` for all `a`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n]

/-- Local Korselt step: if `p` is prime and `p - 1 ∣ n - 1` (with `n ≥ 1`), then
`a ^ n ≡ a [MOD p]` for every `a`. -/
theorem pow_modEq_self_of_sub_one_dvd {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hdvd : p - 1 ∣ n - 1) (a : ℕ) : a ^ n ≡ a [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ((a : ZMod p)) ^ n = (a : ZMod p) := by
    obtain ⟨c, hc⟩ := hdvd
    have hn' : n = (p - 1) * c + 1 := by omega
    rcases eq_or_ne (a : ZMod p) 0 with h0 | h0
    · rw [h0, zero_pow (by omega)]
    · rw [hn', pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow, one_mul]
  exact (ZMod.natCast_eq_natCast_iff (a ^ n) a p).mp (by push_cast; exact key)

/-- Korselt's criterion (sufficiency) for a product of three distinct primes. -/
theorem isCarmichael_of_korselt {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r)
    (hp1 : p - 1 ∣ p * q * r - 1) (hq1 : q - 1 ∣ p * q * r - 1)
    (hr1 : r - 1 ∣ p * q * r - 1) : IsCarmichael (p * q * r) := by
  set n := p * q * r with hn
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hpqr : 1 < n := by
    have : 1 < p * q := by nlinarith
    calc 1 < p * q := this
      _ ≤ p * q * r := Nat.le_mul_of_pos_right _ (by omega)
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hcop_pr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr (by omega)
  have hcop_qr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr (by omega)
  refine ⟨hpqr, ?_, ?_⟩
  · intro hprime
    have hdvd : p ∣ n := ⟨q * r, by rw [hn]; ring⟩
    rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
    · omega
    · have : p * (q * r) = p * 1 := by rw [← mul_assoc, ← hn, h, mul_one]
      have := Nat.eq_of_mul_eq_mul_left (by omega) this
      nlinarith
  · intro a
    have hmp := pow_modEq_self_of_sub_one_dvd hp (by omega) hp1 a
    have hmq := pow_modEq_self_of_sub_one_dvd hq (by omega) hq1 a
    have hmr := pow_modEq_self_of_sub_one_dvd hr (by omega) hr1 a
    have hpq' : a ^ n ≡ a [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop_pq).mp ⟨hmp, hmq⟩
    have hcop : Nat.Coprime (p * q) r := Nat.Coprime.mul hcop_pr hcop_qr
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hpq', hmr⟩

/-- Chernick numbers: for `k ≥ 1`, if `6k+1`, `12k+1`, `18k+1` are all prime then their
product is a Carmichael number with exactly three (distinct) prime factors. -/
theorem isCarmichael_chernick {k : ℕ} (hk : 1 ≤ k) (h6 : (6 * k + 1).Prime)
    (h12 : (12 * k + 1).Prime) (h18 : (18 * k + 1).Prime) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
  have hprod : (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 1296 * k ^ 3 + 396 * k ^ 2 + 36 * k + 1 := by ring
  have hsub : (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 1296 * k ^ 3 + 396 * k ^ 2 + 36 * k := by omega
  refine isCarmichael_of_korselt h6 h12 h18 (by omega) (by omega) ?_ ?_ ?_
  · refine ⟨216 * k ^ 2 + 66 * k + 6, ?_⟩
    rw [hsub]; simp only [Nat.add_sub_cancel]; ring
  · refine ⟨108 * k ^ 2 + 33 * k + 3, ?_⟩
    rw [hsub]; simp only [Nat.add_sub_cancel]; ring
  · refine ⟨72 * k ^ 2 + 22 * k + 2, ?_⟩
    rw [hsub]; simp only [Nat.add_sub_cancel]; ring

/-- The set of Carmichael numbers that are a product of three distinct primes. -/
def ThreePrimeCarmichael : Set ℕ :=
  {n | IsCarmichael n ∧ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r}

/-- **Conditional reduction.** Assuming the (open) Dickson-type hypothesis that the Chernick
triple `6k+1, 12k+1, 18k+1` is simultaneously prime for infinitely many `k`, there are
infinitely many Carmichael numbers with exactly three prime factors. -/
theorem ThreePrimeCarmichaelInfinitude
    (H : ∀ N : ℕ, ∃ k, N < k ∧ (6 * k + 1).Prime ∧ (12 * k + 1).Prime ∧ (18 * k + 1).Prime) :
    ThreePrimeCarmichael.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hkN, h6, h12, h18⟩ := H N
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), ⟨?_, ?_⟩, ?_⟩
  · exact isCarmichael_chernick (by omega) h6 h12 h18
  · exact ⟨6 * k + 1, 12 * k + 1, 18 * k + 1, h6, h12, h18, by omega, by omega, rfl⟩
  · have h1 : k ≤ 6 * k + 1 := by omega
    have h2 : 6 * k + 1 ≤ (6 * k + 1) * (12 * k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h3 : (6 * k + 1) * (12 * k + 1) ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    linarith

/-- Sanity check that the conclusion is not vacuous: `1729 = 7 * 13 * 19` (the Chernick
number for `k = 1`) is a Carmichael number with exactly three prime factors. -/
theorem mem_threePrimeCarmichael_1729 : 1729 ∈ ThreePrimeCarmichael := by
  have h : (1729 : ℕ) = (6 * 1 + 1) * (12 * 1 + 1) * (18 * 1 + 1) := by norm_num
  have h6 : Nat.Prime (6 * 1 + 1) := by norm_num
  have h12 : Nat.Prime (12 * 1 + 1) := by norm_num
  have h18 : Nat.Prime (18 * 1 + 1) := by norm_num
  refine ⟨h ▸ isCarmichael_chernick le_rfl h6 h12 h18, 7, 13, 19, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num

end CarmichaelKorselt
end Brockian

