/-
  Brockian/AbundantClosure.lean — GENERAL closure/structure theorems for the
  abundant / deficient / perfect classes of natural numbers.

  These are citation-grade, fully general lemmas (no numerical specialization)
  feeding the perfect-number frontier of the Brockian program:

    1. `abundant_of_perfect_dvd` — a PROPER multiple of a perfect number is
       abundant.  (Flagship. Divisor-image argument: the divisors of the perfect
       core, scaled up, already sum to `2n`, and the divisor `1` is a genuine
       extra, pushing the divisor sum strictly past `2n`.)
    2. `deficient_of_dvd_deficient` — every POSITIVE divisor of a deficient
       number is deficient.  (The general form is TRUE — proved here by closing
       off the abundant and perfect alternatives via (1) and `Abundant.of_dvd`.)
    3. `prime_deficient` — every prime is deficient.
    4. `exists_prime_factor_of_abundant` — an abundant number has a prime factor.

  Conventions / Mathlib facts used:
    * `Nat.Perfect n  := ∑ i ∈ n.properDivisors, i = n ∧ 0 < n`
    * `Nat.Abundant n := n < ∑ i ∈ n.properDivisors, i`
    * `Nat.Deficient n := ∑ i ∈ n.properDivisors, i < n`
    * the divisor-power sum is `ArithmeticFunction.sigma` (NOT `Nat.sigma`);
      here we work with the raw `∑ i ∈ n.divisors, i` form.

  Verification: AXLE independent @ lean-4.32.0.  No `sorry` / `admit` /
  `native_decide` / `axiom`; the only kernel axioms are the Mathlib standard
  `propext, Classical.choice, Quot.sound`.
-/
import Mathlib

open Finset

namespace Brockian.AbundantClosure

/-- **Flagship closure law.** A proper multiple of a perfect number is abundant.

If `a` is perfect, `a ∣ n`, and `a < n` (so `n` is a *proper* multiple of `a`),
then `n` is abundant.  Write `n = a * k` with `k ≥ 2`.  The scaled divisor set
`{k · d : d ∣ a}` is a set of divisors of `n` summing to `k · σ(a) = k · 2a = 2n`,
and the divisor `1` of `n` is *not* among them (each `k · d ≥ k ≥ 2`), so the full
divisor sum exceeds `2n`, i.e. `n` is abundant. -/
theorem abundant_of_perfect_dvd {a n : ℕ} (ha : Nat.Perfect a) (hdvd : a ∣ n)
    (hlt : a < n) : Nat.Abundant n := by
  have ha0 : 0 < a := ha.2
  obtain ⟨k, rfl⟩ := hdvd
  -- proper multiple ⇒ multiplier ≥ 2
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hlt
    · simp at hlt
    · omega
  have hk0 : k ≠ 0 := by omega
  have hak : a * k ≠ 0 := Nat.mul_ne_zero ha0.ne' hk0
  -- perfect ⇒ divisor sum is exactly 2a
  have hσ : ∑ i ∈ a.divisors, i = 2 * a :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul ha0).mp ha
  -- the scaled divisor set
  set S : Finset ℕ := a.divisors.image (fun d => k * d) with hS
  -- S ⊆ divisors (a * k)
  have hSsub : S ⊆ (a * k).divisors := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hak⟩
    have hdvd' : k * d ∣ k * a := Nat.mul_dvd_mul_left k (Nat.dvd_of_mem_divisors hd)
    rwa [Nat.mul_comm k a] at hdvd'
  -- the scaled divisor set sums to 2·(a·k)
  have hSsum : ∑ x ∈ S, x = 2 * (a * k) := by
    rw [hS, Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hk0 h),
      ← Finset.mul_sum, hσ]
    ring
  -- 1 is a divisor of a·k but not in the scaled set
  have h1mem : (1 : ℕ) ∈ (a * k).divisors := Nat.one_mem_divisors.mpr hak
  have h1S : (1 : ℕ) ∉ S := by
    rw [hS, Finset.mem_image]
    rintro ⟨d, _, hd⟩
    have : k ∣ 1 := ⟨d, hd.symm⟩
    have := Nat.le_of_dvd Nat.one_pos this
    omega
  -- assemble
  have hins : insert 1 S ⊆ (a * k).divisors := Finset.insert_subset h1mem hSsub
  have hsum_ins : ∑ x ∈ insert 1 S, x = 1 + 2 * (a * k) := by
    rw [Finset.sum_insert h1S, hSsum]
  have hle : ∑ x ∈ insert 1 S, x ≤ ∑ x ∈ (a * k).divisors, x :=
    Finset.sum_le_sum_of_subset hins
  rw [Nat.abundant_iff_sum_divisors]
  omega

/-- **Downward closure of deficiency.** Every positive divisor of a deficient
number is deficient.

If `n` is deficient and `d ∣ n` with `d ≥ 1`, then `d` is deficient.  Indeed `d`
cannot be abundant (else `n` would be abundant by `Abundant.of_dvd`) and cannot
be perfect (if `d = n` then `n` is perfect, contradicting deficiency; if `d < n`
then `n` is a proper multiple of a perfect number, hence abundant by
`abundant_of_perfect_dvd`), so the trichotomy forces `d` deficient. -/
theorem deficient_of_dvd_deficient {d n : ℕ} (hn : Nat.Deficient n) (hd : d ∣ n)
    (hd1 : 1 ≤ d) : Nat.Deficient d := by
  have hn0 : n ≠ 0 := (Nat.Deficient.pos hn).ne'
  have hdn : d ≤ n := Nat.le_of_dvd (Nat.Deficient.pos hn) hd
  obtain ⟨hnA, hnP⟩ := (Nat.deficient_iff_not_abundant_and_not_perfect hn0).mp hn
  have hdA : ¬ Nat.Abundant d := fun h => hnA (h.of_dvd hd hn0)
  have hdP : ¬ Nat.Perfect d := by
    intro hp
    rcases lt_or_eq_of_le hdn with hlt | heq
    · exact hnA (abundant_of_perfect_dvd hp hd hlt)
    · exact hnP (heq ▸ hp)
  rcases Nat.deficient_or_perfect_or_abundant (show (0 : ℕ) ≠ d by omega) with h | h | h
  · exact h
  · exact absurd h hdA
  · exact absurd h hdP

/-- **Every prime is deficient.**  (Thin wrapper over `Nat.Prime.deficient`.) -/
theorem prime_deficient {p : ℕ} (hp : p.Prime) : Nat.Deficient p :=
  hp.deficient

/-- **An abundant number has a prime factor.**  Any abundant `n` satisfies
`n ≠ 1` (as `1` is not abundant: its proper-divisor sum is `0`), so it admits a
prime divisor. -/
theorem exists_prime_factor_of_abundant {n : ℕ} (hn : Nat.Abundant n) :
    ∃ p, p.Prime ∧ p ∣ n := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact absurd hn (by decide)
  exact Nat.exists_prime_and_dvd hn1

/-- **Convenience corollary of the flagship law:** a proper multiple of `6`
(the least perfect number) is abundant. -/
theorem abundant_of_six_dvd {n : ℕ} (hdvd : 6 ∣ n) (hlt : 6 < n) : Nat.Abundant n :=
  abundant_of_perfect_dvd ⟨by decide, by decide⟩ hdvd hlt

end Brockian.AbundantClosure
