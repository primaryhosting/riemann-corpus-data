import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-!
## The proposed theorem is false

The requested statement

```
theorem odd_zumkeller_div_three : ∀ n, Odd n → Zumkeller n → 3 ∣ n
```

is **not** provable: it is refuted by `N = 5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`,
which is odd, not divisible by `3`, and Zumkeller.  Indeed `σ(N) = 10799308800`, and the six
divisors

`1, 23, 391, 135575, 8107385, 5391411025`

sum to `5399654400 = σ(N)/2`.

The original statement is therefore kept below only as a comment, and we prove its negation.
-/

/-- The divisor-sum function is multiplicative: for coprime `m` and `k`,
`σ(m * k) = σ(m) * σ(k)`. -/
lemma sum_divisors_mul_of_coprime {m k : ℕ} (h : m.Coprime k) :
    ∑ d ∈ (m * k).divisors, d = (∑ d ∈ m.divisors, d) * (∑ d ∈ k.divisors, d) := by
  simpa [ArithmeticFunction.sigma_one_apply] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

/-- `σ(5391411025) = 10799308800`, computed from the factorization
`5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`. -/
lemma sum_divisors_5391411025 : ∑ d ∈ (5391411025 : ℕ).divisors, d = 10799308800 := by
  have h : (5391411025 : ℕ) = 25 * 7 * 11 * 13 * 17 * 19 * 23 * 29 := by norm_num
  rw [h, sum_divisors_mul_of_coprime (by norm_num), sum_divisors_mul_of_coprime (by norm_num),
    sum_divisors_mul_of_coprime (by norm_num), sum_divisors_mul_of_coprime (by norm_num),
    sum_divisors_mul_of_coprime (by norm_num), sum_divisors_mul_of_coprime (by norm_num),
    sum_divisors_mul_of_coprime (by norm_num)]
  decide

/-- The six divisors `1, 23, 391, 135575, 8107385, 5391411025` of `5391411025` sum to exactly
half of `σ(5391411025)`; hence `5391411025` is a Zumkeller number. -/
theorem zumkeller_5391411025 : Zumkeller 5391411025 := by
  refine ⟨{1, 23, 391, 135575, 8107385, 5391411025}, ?_, ?_⟩
  · intro d hd
    rw [Nat.mem_divisors]
    refine ⟨?_, by norm_num⟩
    fin_cases hd <;> norm_num
  · rw [sum_divisors_5391411025]
    decide

/-- `5391411025` is odd. -/
theorem odd_5391411025 : Odd (5391411025 : ℕ) := by
  rw [Nat.odd_iff]

/-- `5391411025` is not divisible by `3`. -/
theorem not_three_dvd_5391411025 : ¬ (3 ∣ (5391411025 : ℕ)) := by decide

/-
The requested statement, which is false:

theorem odd_zumkeller_div_three : ∀ n, Odd n → Zumkeller n → 3 ∣ n
-/

/-- **The conjecture "every odd Zumkeller number is divisible by 3" is false.**
The counterexample is `5391411025 = 5^2 * 7 * 11 * 13 * 17 * 19 * 23 * 29`. -/
theorem not_odd_zumkeller_div_three : ¬ (∀ n : ℕ, Odd n → Zumkeller n → 3 ∣ n) := by
  intro h
  exact not_three_dvd_5391411025 (h 5391411025 odd_5391411025 zumkeller_5391411025)

end Brockian.ZumkellerNumbers

