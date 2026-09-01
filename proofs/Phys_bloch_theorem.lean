import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option grind.warning false

namespace Phys

/-- **Translation invariance of a periodic Schrödinger operator.**

If the potential `V` has period `a` and `ψ` solves the stationary Schrödinger equation
`-ψ'' + V ψ = E ψ`, then the translate `x ↦ ψ (x + a)` solves the same equation.
This is the structural input to Bloch's theorem: the translation operator commutes with
the Hamiltonian, so on a nondegenerate eigenspace it must act on the eigenstate by a scalar. -/
theorem translate_solution_of_periodic_potential
    {E : ℂ} {a : ℝ} {V ψ : ℝ → ℂ}
    (hV : ∀ x : ℝ, V (x + a) = V x)
    (hψ : ∀ x : ℝ, -deriv (deriv ψ) x + V x * ψ x = E * ψ x) :
    ∀ x : ℝ, -deriv (deriv (fun y : ℝ => ψ (y + a))) x + V x * ψ (x + a)
      = E * ψ (x + a) := by
  intro x
  have h1 : deriv (fun y : ℝ => ψ (y + a)) = fun y : ℝ => deriv ψ (y + a) :=
    funext fun y => deriv_comp_add_const ψ a y
  rw [h1, deriv_comp_add_const (deriv ψ) a x, ← hV x]
  exact hψ (x + a)

/-- **Bloch's theorem.**

Let `ψ` be an eigenstate of a Hamiltonian invariant under translation by the lattice
period `a ≠ 0`.  Nondegeneracy of the eigenvalue forces the translate of `ψ` to be a scalar
multiple of `ψ`, i.e. `ψ (x + a) = c * ψ x`, and conservation of probability forces `‖c‖ = 1`.
Under exactly these hypotheses `ψ` is a Bloch wave: there is a crystal momentum `k`
with `e^{i k a} = c` and a function `u` of period `a` such that

  `ψ x = e^{i k x} * u x`  for all `x`. -/
theorem bloch_theorem {a : ℝ} {ψ : ℝ → ℂ} {c : ℂ} (ha : a ≠ 0) (hc : ‖c‖ = 1)
    (hψ : ∀ x : ℝ, ψ (x + a) = c * ψ x) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ,
      Complex.exp (k * a * Complex.I) = c ∧
      (∀ x : ℝ, u (x + a) = u x) ∧
      (∀ x : ℝ, ψ x = Complex.exp (k * x * Complex.I) * u x) := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff c).mp hc
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  refine ⟨θ / a, fun x => Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) * ψ x,
    ?_, ?_, ?_⟩
  · have h : ((θ / a : ℝ) : ℂ) * (a : ℂ) = ((θ : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [h, hθ]
  · -- periodicity of `u`
    intro x
    have hcp : Complex.exp (-((θ / a : ℝ) : ℂ) * (a : ℂ) * Complex.I) * c = 1 := by
      have h1 : (-((θ / a : ℝ) : ℂ)) * (a : ℂ) = -((θ : ℝ) : ℂ) := by
        push_cast
        field_simp
      rw [h1, ← hθ, ← Complex.exp_add]
      have h2 : -((θ : ℝ) : ℂ) * Complex.I + ((θ : ℝ) : ℂ) * Complex.I = 0 := by ring
      rw [h2, Complex.exp_zero]
    have hsplit : Complex.exp (-((θ / a : ℝ) : ℂ) * ((x : ℂ) + (a : ℂ)) * Complex.I)
        = Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I)
          * Complex.exp (-((θ / a : ℝ) : ℂ) * (a : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      ring_nf
    simp only [Complex.ofReal_add]
    rw [hψ x, hsplit]
    calc Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I)
          * Complex.exp (-((θ / a : ℝ) : ℂ) * (a : ℂ) * Complex.I) * (c * ψ x)
        = Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) * ψ x
          * (Complex.exp (-((θ / a : ℝ) : ℂ) * (a : ℂ) * Complex.I) * c) := by ring
      _ = Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) * ψ x := by
          rw [hcp, mul_one]
  · -- the Bloch factorisation
    intro x
    have h : Complex.exp (((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I)
        * Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have h2 : ((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I
          + -((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I = 0 := by ring
      rw [h2, Complex.exp_zero]
    calc ψ x = 1 * ψ x := (one_mul _).symm
      _ = Complex.exp (((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I)
            * (Complex.exp (-((θ / a : ℝ) : ℂ) * (x : ℂ) * Complex.I) * ψ x) := by
          rw [← mul_assoc, h]

end Phys

