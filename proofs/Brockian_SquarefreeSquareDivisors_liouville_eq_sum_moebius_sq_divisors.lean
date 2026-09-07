import Mathlib

/-!
# Two square-divisor identities (parity/sieve arithmetic)

Both use Mathlib's `ArithmeticFunction.moebius` (μ) and `ArithmeticFunction.liouville` (λ).
Neither identity is currently in Mathlib. Compile against a bare `import Mathlib`; do not cite
any non-core/Archive namespaces or invented lemmas.

Uses Mathlib's `ArithmeticFunction.liouville` (added upstream at 4.32).

The proofs use the decomposition `n = s * r ^ 2` with `s` squarefree (`Nat.sq_mul_squarefree`).
Since `s` is squarefree, `d ^ 2 ∣ n ↔ d ∣ r`, so both sums are sums over the divisors of `r`.
-/


namespace Brockian.SquarefreeSquareDivisors

open ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

/-- A product `s * m ^ 2` with `m ≠ 1` is never squarefree. -/
lemma not_squarefree_mul_sq {s m : ℕ} (hm : m ≠ 1) : ¬ Squarefree (s * m ^ 2) := by
  intro hsq
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm
  have hdvd : p * p ∣ s * m ^ 2 :=
    Dvd.dvd.mul_left (by rw [sq]; exact mul_dvd_mul hpm hpm) s
  exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hdvd))

/-- If `s` is squarefree then the `d` with `d ^ 2 ∣ s * r ^ 2` are exactly the divisors of `r`. -/
lemma sq_dvd_iff_dvd {s r : ℕ} (hs : Squarefree s) (hr : r ≠ 0) (d : ℕ) :
    d ^ 2 ∣ s * r ^ 2 ↔ d ∣ r := by
  have hs0 : s ≠ 0 := hs.ne_zero
  have hn0 : s * r ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h
      omega
    rw [← Nat.factorization_le_iff_dvd hd0 hr]
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hn0] at h
    intro p
    have h1 := h p
    simp [Nat.factorization_mul hs0 (pow_ne_zero 2 hr), Nat.factorization_pow] at h1 ⊢
    have h2 : s.factorization p ≤ 1 := hs.natFactorization_le_one p
    omega
  · intro h
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd h 2) s

/-- The square-divisor filter of `s * r ^ 2` (with `s` squarefree) is `r.divisors`. -/
lemma filter_sq_dvd {s r : ℕ} (hs : Squarefree s) (hr : r ≠ 0) (hs0 : s ≠ 0) :
    (s * r ^ 2).divisors.filter (fun d => d ^ 2 ∣ s * r ^ 2) = r.divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, sq_dvd_iff_dvd hs hr]
  constructor
  · rintro ⟨-, hd⟩
    exact ⟨hd, hr⟩
  · rintro ⟨hd, -⟩
    exact ⟨⟨Dvd.dvd.mul_left (hd.trans (dvd_pow_self r two_ne_zero)) s, by positivity⟩, hd⟩

/-- `∑_{d ∣ r} μ d = [r = 1]`. -/
lemma sum_moebius_divisors (r : ℕ) :
    ∑ d ∈ r.divisors, μ d = if r = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℤ)) (x := r),
    moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- `μ (s * r ^ 2) ^ 2 = [r = 1]` for `s` squarefree. -/
lemma moebius_sq_apply {s r : ℕ} (hs : Squarefree s) :
    (μ (s * r ^ 2)) ^ 2 = if r = 1 then 1 else 0 := by
  by_cases h : r = 1
  · subst h
    simpa using moebius_sq_eq_one_of_squarefree (by simpa using hs)
  · rw [if_neg h, moebius_eq_zero_of_not_squarefree (not_squarefree_mul_sq h)]
    simp

/-- For a proper divisor `d` of `r`, the quotient `(s * r ^ 2) / d ^ 2` is not squarefree. -/
lemma moebius_div_sq_eq_zero {s r d : ℕ} (hr : r ≠ 0) (hd : d ∣ r) (hdr : d ≠ r) :
    μ ((s * r ^ 2) / d ^ 2) = 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 1 := by rintro rfl; simp at hdr
  have hd0 : d ≠ 0 := by rintro rfl; simp at hr
  have heq : (s * (d * k) ^ 2) / d ^ 2 = s * k ^ 2 := by
    rw [mul_pow, ← mul_assoc, mul_comm s (d ^ 2), mul_assoc,
      Nat.mul_div_cancel_left _ (by positivity)]
  rw [heq, moebius_eq_zero_of_not_squarefree (not_squarefree_mul_sq hk)]

/-- `λ (s * r ^ 2) = μ s` for `s` squarefree: the square factor does not change the parity of the
number of prime factors. -/
lemma liouville_apply_eq_moebius {s r : ℕ} (hs : Squarefree s) (hr : r ≠ 0) (hs0 : s ≠ 0) :
    liouville (s * r ^ 2) = μ s := by
  rw [liouville_apply (by positivity), ArithmeticFunction.cardFactors_mul hs0 (by positivity),
    ArithmeticFunction.cardFactors_pow, moebius_apply_of_squarefree hs, pow_add, pow_mul]
  simp

/-- **Squarefree indicator via square-divisors.** For `n ≥ 1`,
`μ(n)^2 = ∑_{d : d^2 ∣ n} μ(d)`.  (`μ(n)^2` is 1 iff `n` is squarefree; the right side is the
classical convolution proof of that indicator.  Multiplicative on both sides; check on prime powers
`p^a`: RHS `= ∑_{2j ≤ a} μ(p^j) = 1 + (-1) = 0` for `a ≥ 2`, `= 1` for `a ∈ {0,1}`.) -/
theorem moebius_sq_eq_sum_sq_divisors (n : ℕ) (hn : n ≠ 0) :
    (ArithmeticFunction.moebius n) ^ 2
      = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), ArithmeticFunction.moebius d := by
  obtain ⟨s, r, rfl, hs⟩ := Nat.sq_mul_squarefree n
  have hr : r ≠ 0 := by rintro rfl; simp at hn
  have hs0 : s ≠ 0 := by rintro rfl; simp at hn
  rw [mul_comm] at hn ⊢
  rw [filter_sq_dvd hs hr hs0, sum_moebius_divisors r, moebius_sq_apply hs]

/-- **Liouville as Möbius over square-divisors.** For `n ≥ 1`,
`λ(n) = ∑_{d : d^2 ∣ n} μ(n / d^2)`.  (Dirichlet-series identity `L(λ,s) = ζ(2s)/ζ(s)`; equivalently
`λ = μ ⋆ 𝟙_squares`.  Multiplicative; check on prime powers.) -/
theorem liouville_eq_sum_moebius_sq_divisors (n : ℕ) (hn : n ≠ 0) :
    ArithmeticFunction.liouville n
      = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), ArithmeticFunction.moebius (n / d ^ 2) := by
  obtain ⟨s, r, rfl, hs⟩ := Nat.sq_mul_squarefree n
  have hr : r ≠ 0 := by rintro rfl; simp at hn
  have hs0 : s ≠ 0 := by rintro rfl; simp at hn
  rw [mul_comm] at hn ⊢
  rw [filter_sq_dvd hs hr hs0, liouville_apply_eq_moebius hs hr hs0]
  rw [Finset.sum_eq_single r]
  · congr 1
    exact (Nat.mul_div_cancel s (by positivity : 0 < r ^ 2)).symm
  · intro d hd hdr
    exact moebius_div_sq_eq_zero hr (Nat.dvd_of_mem_divisors hd) hdr
  · intro h
    exact absurd (Nat.mem_divisors_self r hr) h

end Brockian.SquarefreeSquareDivisors
