import Mathlib
/-!
# Euler totient as a Möbius convolution.
Uses Mathlib's `Nat.totient` and `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve
/-- Euler's totient as the Dirichlet convolution `φ = μ ⋆ id`:
`φ(n) = ∑_{d ∣ n} μ(d) · (n / d)`.  (Sanity: `n=6`: `φ(6)=2`; RHS `= 6 − 3 − 2 + 1 = 2`.) -/
theorem totient_eq_sum_moebius (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℤ)
      = ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ) := by
  -- Möbius inversion applied to `∑_{d ∣ n} φ(d) = n` (`Nat.sum_totient`).
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun i => (Nat.totient i : ℤ)) (g := fun m => (m : ℤ))).mp
    (by
      intro m _
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.sum_totient m))
    n (Nat.pos_of_ne_zero hn)
  rw [← h, ← Nat.sum_divisorsAntidiagonal
    (f := fun a b => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))]
  rfl
end BrockianSieve

