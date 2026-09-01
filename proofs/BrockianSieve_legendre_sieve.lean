import Mathlib

/-!
# Legendre's sieve (inclusion–exclusion / sieve of Eratosthenes)

Uses Mathlib's `ArithmeticFunction.moebius` (μ). Compile against a bare `import Mathlib`; do not
cite any non-core/Archive namespaces or invented lemmas.
-/

namespace BrockianSieve

/-- **Legendre's sieve.** The number of integers in `[1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`.  Non-squarefree divisors contribute `0` (μ vanishes), so no squarefree
hypothesis on `P` is needed.  This is the foundational inclusion–exclusion identity of sieve theory.
(Sanity: `x = 10`, `P = 6`: LHS `= #{1,5,7} = 3`; RHS `= 10 − 5 − 3 + 1 = 3`.) -/
theorem legendre_sieve (x P : ℕ) (hP : P ≠ 0) :
    (((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ)
      = ∑ d ∈ P.divisors, ArithmeticFunction.moebius d * ((x / d : ℕ) : ℤ) := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  -- Coprimality to `P` is detected by `∑_{d ∣ gcd (n, P)} μ d`.
  have key : ∀ n ∈ Finset.Ioc 0 x,
      (if Nat.Coprime n P then (1 : ℤ) else 0)
        = ∑ d ∈ P.divisors, if d ∣ n then ArithmeticFunction.moebius d else 0 := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : n ≠ 0 := hn.1.ne'
    have h1 : (Nat.gcd n P).divisors = P.divisors.filter (· ∣ n) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h2, h3⟩, -⟩; exact ⟨⟨h3, hP⟩, h2⟩
      · rintro ⟨⟨h3, -⟩, h2⟩; exact ⟨⟨h2, h3⟩, Nat.gcd_ne_zero_left hn0⟩
    have h2 : ∑ d ∈ (Nat.gcd n P).divisors, ArithmeticFunction.moebius d
        = if Nat.gcd n P = 1 then 1 else 0 := by
      rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
      simp [ArithmeticFunction.one_apply]
    rw [← Finset.sum_filter, ← h1, h2]
  calc (((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ)
      = ∑ n ∈ Finset.Ioc 0 x, (if Nat.Coprime n P then (1 : ℤ) else 0) := by
        rw [hIcc, Finset.card_filter]; push_cast; rfl
    _ = ∑ n ∈ Finset.Ioc 0 x, ∑ d ∈ P.divisors,
          (if d ∣ n then ArithmeticFunction.moebius d else 0) := Finset.sum_congr rfl key
    _ = ∑ d ∈ P.divisors, ∑ n ∈ Finset.Ioc 0 x,
          (if d ∣ n then ArithmeticFunction.moebius d else 0) := Finset.sum_comm
    _ = ∑ d ∈ P.divisors, ArithmeticFunction.moebius d * ((x / d : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
          mul_comm]

end BrockianSieve

