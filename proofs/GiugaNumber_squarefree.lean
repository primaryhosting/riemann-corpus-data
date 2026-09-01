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

def GiugaNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

def OddGiugaExists : Prop := ∃ n : ℕ, Odd n ∧ GiugaNumber n

/-- A Giuga number is squarefree: if `p * p ∣ n` then `p ∣ n / p` as well as
`p ∣ n / p - 1`, forcing `p ∣ 1`. -/
lemma GiugaNumber.squarefree {n : ℕ} (h : GiugaNumber n) : Squarefree n := by
  obtain ⟨hn1, -, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hcon
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hcon
  have h1 : p ∣ n / p - 1 := hdvd p hp hpn
  obtain ⟨k, hk⟩ := hcon
  have h2 : p ∣ n / p := ⟨k, by rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have hone : p ∣ 1 := by
    have := Nat.dvd_sub h2 h1
    rwa [Nat.sub_sub_self hpos] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

theorem giugaNumber_three_primes {n : ℕ} (h : GiugaNumber n) : 3 ≤ n.primeFactors.card := by
  have hsq := h.squarefree
  obtain ⟨hn1, hnp, hdvd⟩ := h
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
  by_contra hcon
  push_neg at hcon
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  have hpos : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr hne
  interval_cases hc : n.primeFactors.card
  · -- one prime factor: n is prime
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have : n = p := by rw [← hprod, hp, Finset.prod_singleton]
    exact hnp (this ▸ (Nat.prime_of_mem_primeFactors hmem))
  · -- two prime factors: n = p * q with p ∣ q - 1 and q ∣ p - 1
    obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hc
    have hpm : p ∈ n.primeFactors := by rw [hs]; simp
    have hqm : q ∈ n.primeFactors := by rw [hs]; simp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
    have hn : n = p * q := by
      rw [← hprod, hs, Finset.prod_pair hpq]
    have hdp : p ∣ q - 1 := by
      have := hdvd p hp (Nat.dvd_of_mem_primeFactors hpm)
      rwa [hn, Nat.mul_div_cancel_left _ hp.pos] at this
    have hdq : q ∣ p - 1 := by
      have := hdvd q hq (Nat.dvd_of_mem_primeFactors hqm)
      rwa [hn, mul_comm, Nat.mul_div_cancel_left _ hq.pos] at this
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    have h1 : p ≤ q - 1 := Nat.le_of_dvd (by omega) hdp
    have h2 : q ≤ p - 1 := Nat.le_of_dvd (by omega) hdq
    omega

