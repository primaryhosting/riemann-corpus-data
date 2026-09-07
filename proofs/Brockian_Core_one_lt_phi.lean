/-
  Brockian/Core.lean — the algebraic core of the Brockian Universal Pentagonal Law.

  Citation-grade Mathlib-4.32 port of the φ-algebra, fifth-root, ray-ring, and
  Dirichlet-on-rays facts, distilled from the legacy sources `GoldenRatio.lean`,
  `BrockianUniversalLaw.lean`, and `RayPartition.lean` (written for ~Mathlib 4.14).

  Contents:
    * φ-algebra:  `phi_sq` (φ² = φ+1), `phi_pos`, `one_lt_phi`,
                  `cos_pi_div_five_eq_phi_div_two`, `cos_2pi_5` (cos(2π/5) = (φ−1)/2)
    * fifth root: `fifth_root_of_unity`  ((exp 2πi/5)⁵ = 1)
    * Binet:      `binet_formula`, `fib_five_dvd`
    * ray ring:   `Ray`, `mem_ray_iff`, `ray_add`, `ray_mul`, `ray_zero_iff_dvd`
    * Dirichlet:  `each_ray_has_infinitely_many_primes`, `ray_ne_zero_infinite`

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Brockian.Core

/-! ### The golden ratio φ -/

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

@[inherit_doc] scoped notation "φ" => Brockian.Core.phi

/-- φ satisfies the defining quadratic φ² = φ + 1. -/
theorem phi_sq : φ ^ 2 = φ + 1 := by
  unfold phi
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  field_simp
  ring_nf
  rw [Real.sq_sqrt h5]
  ring

/-- φ is positive. -/
theorem phi_pos : 0 < φ := by
  unfold phi
  positivity

/-- φ > 1 (it is the larger root of x² = x + 1). -/
theorem one_lt_phi : 1 < φ := by
  unfold phi
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h1 : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ### Cosines at the pentagon angles -/

/-- The pentagon link: cos(π/5) = φ/2. -/
theorem cos_pi_div_five_eq_phi_div_two : Real.cos (Real.pi / 5) = φ / 2 := by
  rw [Real.cos_pi_div_five]
  unfold phi
  ring

/-- **cos(2π/5) = (φ − 1)/2.** The eigenvalue link forcing φ into the pentagon.
Ported from `BrockianUniversalLaw.cos_2pi_5` (which relied on `Real.cos_pi_div_five`
plus the double-angle identity). -/
theorem cos_2pi_5 : Real.cos (2 * Real.pi / 5) = (φ - 1) / 2 := by
  have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have hdiv : (2 * Real.pi / 5) = (2 * (Real.pi / 5)) := by ring
  have htwo : Real.cos (2 * (Real.pi / 5)) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
    simpa using (Real.cos_two_mul (Real.pi / 5))
  calc
    Real.cos (2 * Real.pi / 5)
        = Real.cos (2 * (Real.pi / 5)) := by rw [hdiv]
    _   = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := htwo
    _   = 2 * (((1 + Real.sqrt 5) / 4) ^ 2) - 1 := by rw [hcos]
    _   = (Real.sqrt 5 - 1) / 4 := by
          have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
          ring_nf
          ring_nf at h5
          rw [h5]; ring
    _   = (φ - 1) / 2 := by unfold phi; ring

/-! ### Fifth roots of unity -/

/-- The pentagon vertex `exp(2πi/5)` is a fifth root of unity. -/
theorem fifth_root_of_unity :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5)) ^ 5 = 1 := by
  rw [← Complex.exp_nat_mul]
  have h : ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_two_pi_mul_I]

/-! ### Binet's formula and Fibonacci divisibility -/

/-- **Binet's formula** for the Fibonacci numbers in terms of φ.
Ported (the legacy source left this as `sorry`); discharged via Mathlib's
`Real.coe_fib_eq`, after identifying φ = `Real.goldenRatio` and
`1 − φ = Real.goldenConj`. -/
theorem binet_formula (n : ℕ) :
    (Nat.fib n : ℝ) = (φ ^ n - (1 - φ) ^ n) / Real.sqrt 5 := by
  have hg : φ = Real.goldenRatio := by unfold phi Real.goldenRatio; ring
  have hc : (1 - φ) = Real.goldenConj := by unfold phi Real.goldenConj; ring
  rw [hc, hg]
  exact Real.coe_fib_eq n

/-- Every fifth Fibonacci number is divisible by 5 (`fib 5 = 5 ∣ fib (5k)`).
Ported (legacy `sorry`); discharged via `Nat.fib_dvd`. -/
theorem fib_five_dvd (k : ℕ) : 5 ∣ Nat.fib (5 * k) := by
  simpa [show Nat.fib 5 = 5 from by decide] using
    Nat.fib_dvd 5 (5 * k) ⟨k, rfl⟩

/-! ### Ray partition as a ring homomorphism on residues -/

/-- A ray mod `p`: the naturals congruent to `i : ZMod p`. -/
def Ray (p : ℕ) (i : ZMod p) : Set ℕ := {n : ℕ | (n : ZMod p) = i}

@[simp] theorem mem_ray_iff (p : ℕ) (i : ZMod p) (n : ℕ) :
    n ∈ Ray p i ↔ (n : ZMod p) = i := Iff.rfl

/-- Rays add: `m ∈ Ray p i`, `n ∈ Ray p j` ⇒ `m + n ∈ Ray p (i + j)`
(the residue map `ℕ → ZMod p` is additive). -/
theorem ray_add {p : ℕ} {i j : ZMod p} {m n : ℕ}
    (hm : m ∈ Ray p i) (hn : n ∈ Ray p j) : m + n ∈ Ray p (i + j) := by
  simp only [mem_ray_iff] at hm hn ⊢
  push_cast
  rw [hm, hn]

/-- Rays multiply: `m ∈ Ray p i`, `n ∈ Ray p j` ⇒ `m * n ∈ Ray p (i * j)`
(the residue map `ℕ → ZMod p` is multiplicative). -/
theorem ray_mul {p : ℕ} {i j : ZMod p} {m n : ℕ}
    (hm : m ∈ Ray p i) (hn : n ∈ Ray p j) : m * n ∈ Ray p (i * j) := by
  simp only [mem_ray_iff] at hm hn ⊢
  push_cast
  rw [hm, hn]

/-- **Ray-zero singularity.** The zero ray `Ray p 0` is exactly the multiples of `p`
— the degenerate ray `E` containing the modulus. -/
theorem ray_zero_iff_dvd (p : ℕ) (n : ℕ) : n ∈ Ray p 0 ↔ p ∣ n := by
  rw [mem_ray_iff]
  exact ZMod.natCast_eq_zero_iff n p

/-! ### Dirichlet on rays -/

/-- **Dirichlet on rays.** Every unit ray mod 5 (i.e. `i ∈ {1,2,3,4}`) contains
infinitely many primes. Discharged via Mathlib's Dirichlet theorem
`Nat.infinite_setOf_prime_and_eq_mod`. -/
theorem each_ray_has_infinitely_many_primes (i : ZMod 5) (hi : IsUnit i) :
    {p : ℕ | p.Prime ∧ p ∈ Ray 5 i}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod hi

/-- The four non-zero rays mod 5 each contain infinitely many primes (ZMod 5 is a
field, so `i ≠ 0` is the same as `IsUnit i`). -/
theorem ray_ne_zero_infinite (i : ZMod 5) (hi : i ≠ 0) :
    {p : ℕ | p.Prime ∧ p ∈ Ray 5 i}.Infinite := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact each_ray_has_infinitely_many_primes i (isUnit_iff_ne_zero.mpr hi)

end Brockian.Core
