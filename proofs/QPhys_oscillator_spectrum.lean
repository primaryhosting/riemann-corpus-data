import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

namespace QPhys

open Polynomial

/-! ## The Fock (Bargmann) model of the quantum harmonic oscillator

We realise the oscillator on the space `ℂ[X]` of polynomials, the algebraic Fock space
spanned by the number states `Xⁿ`.  The annihilation operator is differentiation and the
creation operator is multiplication by `X`; these satisfy the canonical commutation
relation `[a, a†] = 1`.  The Hamiltonian is `H = ℏω (a†a + ½)`. -/

/-- The annihilation (lowering) operator `a`, acting on the Fock space `ℂ[X]`. -/
noncomputable def annihilate : ℂ[X] →ₗ[ℂ] ℂ[X] := Polynomial.derivative

/-- The creation (raising) operator `a†`, acting on the Fock space `ℂ[X]`. -/
noncomputable def create : ℂ[X] →ₗ[ℂ] ℂ[X] := LinearMap.mulLeft ℂ (X : ℂ[X])

/-- The number operator `N = a† a`. -/
noncomputable def numberOp : ℂ[X] →ₗ[ℂ] ℂ[X] := create ∘ₗ annihilate

/-- The harmonic-oscillator Hamiltonian `H = ℏω (a†a + ½)`. -/
noncomputable def hamiltonian (hbar omega : ℝ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ((hbar * omega : ℝ) : ℂ) • (numberOp + (1 / 2 : ℂ) • LinearMap.id)

/-- The canonical commutation relation `[a, a†] = 1`. -/
theorem ladder_commutator (p : ℂ[X]) :
    annihilate (create p) - create (annihilate p) = p := by
  simp [annihilate, create, derivative_mul]

/-- The number operator is diagonal in the number basis: `N` multiplies the `n`-th
coefficient by `n`. -/
theorem coeff_numberOp (p : ℂ[X]) (n : ℕ) : (numberOp p).coeff n = n * p.coeff n := by
  cases n with
  | zero => simp [numberOp, create, annihilate]
  | succ m =>
      simp [numberOp, create, annihilate, coeff_X_mul, coeff_derivative]
      ring

theorem coeff_hamiltonian (hbar omega : ℝ) (p : ℂ[X]) (n : ℕ) :
    (hamiltonian hbar omega p).coeff n
      = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2) * p.coeff n := by
  simp [hamiltonian, coeff_numberOp]
  ring

/-- The number state `Xⁿ` is an eigenvector of `H` with eigenvalue `ℏω (n + ½)`. -/
theorem hamiltonian_number_state (hbar omega : ℝ) (n : ℕ) :
    hamiltonian hbar omega (X ^ n) = (((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)) • (X ^ n) := by
  ext m
  rw [coeff_hamiltonian]
  simp only [coeff_X_pow, coeff_smul, smul_eq_mul]
  rcases eq_or_ne m n with h | h
  · simp [h]
  · simp [h]

theorem hamiltonian_apply (hbar omega : ℝ) (p : ℂ[X]) :
    hamiltonian hbar omega p
      = ((hbar * omega : ℝ) : ℂ) • (numberOp p + (1 / 2 : ℂ) • p) := by
  simp [hamiltonian]

/-- Commuting the number operator past the raising operator: `N a† = a† (N + 1)`. -/
theorem numberOp_create (p : ℂ[X]) : numberOp (create p) = create p + create (numberOp p) := by
  simp [numberOp, create, annihilate, derivative_mul]
  ring

/-- Commuting the number operator past the lowering operator: `N a = a (N - 1)`. -/
theorem numberOp_annihilate (p : ℂ[X]) :
    numberOp (annihilate p) = annihilate (numberOp p) - annihilate p := by
  simp [numberOp, create, annihilate, derivative_mul]

/-- The raising operator increases the energy by one quantum `ℏω`. -/
theorem hamiltonian_create (hbar omega : ℝ) (p : ℂ[X]) :
    hamiltonian hbar omega (create p)
      = create (hamiltonian hbar omega p) + ((hbar * omega : ℝ) : ℂ) • create p := by
  rw [hamiltonian_apply, hamiltonian_apply, numberOp_create, map_smul, map_add, map_smul]
  module

/-- The lowering operator decreases the energy by one quantum `ℏω`. -/
theorem hamiltonian_annihilate (hbar omega : ℝ) (p : ℂ[X]) :
    hamiltonian hbar omega (annihilate p)
      = annihilate (hamiltonian hbar omega p) - ((hbar * omega : ℝ) : ℂ) • annihilate p := by
  rw [hamiltonian_apply, hamiltonian_apply, numberOp_annihilate, map_smul, map_add, map_smul]
  module

/-- **Spectrum of the quantum harmonic oscillator.**  On the Fock space `ℂ[X]`, with
`a = d/dX` and `a† = X·(-)` the ladder operators and `H = ℏω (a†a + ½)`, the set of
eigenvalues of `H` is exactly `{ℏω (n + ½) : n ∈ ℕ}`. -/
theorem oscillator_spectrum (hbar omega : ℝ) :
    {l : ℂ | ∃ p : ℂ[X], p ≠ 0 ∧ hamiltonian hbar omega p = l • p}
      = {l : ℂ | ∃ n : ℕ, l = ((hbar * omega : ℝ) : ℂ) * ((n : ℂ) + 1 / 2)} := by
  ext l
  constructor
  · rintro ⟨p, hp, hEq⟩
    refine ⟨p.natDegree, ?_⟩
    have hc : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have h := congrArg (fun q => Polynomial.coeff q p.natDegree) hEq
    simp only [coeff_hamiltonian, Polynomial.coeff_smul, smul_eq_mul] at h
    field_simp at h
    linear_combination -h / 2
  · rintro ⟨n, rfl⟩
    exact ⟨X ^ n, pow_ne_zero n Polynomial.X_ne_zero, hamiltonian_number_state hbar omega n⟩

end QPhys

