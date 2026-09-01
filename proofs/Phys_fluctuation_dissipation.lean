import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

/-- The partition function of a finite classical system with energies `H`,
inverse temperature `β`, perturbed by an external field `f` conjugate to the
observable `A`: the perturbed Hamiltonian is `H i - f * A i`. -/
noncomputable def partition {ι : Type*} [Fintype ι] (β : ℝ) (H A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * (H i - f * A i))

/-- The equilibrium (Gibbs) expectation value of the observable `B` in the
field-perturbed ensemble. -/
noncomputable def expect {ι : Type*} [Fintype ι] (β : ℝ) (H A : ι → ℝ) (B : ι → ℝ) (f : ℝ) : ℝ :=
  (∑ i, B i * Real.exp (-β * (H i - f * A i))) / partition β H A f

/-- The equilibrium connected correlation (covariance) of two observables `A`
and `B` in the unperturbed Gibbs ensemble. -/
noncomputable def correlation {ι : Type*} [Fintype ι] (β : ℝ) (H : ι → ℝ) (A B : ι → ℝ) : ℝ :=
  expect β H A (fun i => A i * B i) 0 - expect β H A A 0 * expect β H A B 0

/-- **Fluctuation–dissipation theorem** (classical, finite state space).

The static linear response of the equilibrium average of an observable `B` to an
external field `f` coupling to the observable `A` (i.e. the susceptibility
`χ = d⟨B⟩_f / df` at `f = 0`) equals `β` times the equilibrium correlation
(covariance) of `A` and `B` in the unperturbed ensemble. -/
theorem fluctuation_dissipation {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (H A B : ι → ℝ) :
    HasDerivAt (expect β H A B) (β * correlation β H A B) 0 := by
  have hexp : ∀ i : ι, ∀ f : ℝ,
      HasDerivAt (fun g : ℝ => Real.exp (-β * (H i - g * A i)))
        (β * A i * Real.exp (-β * (H i - f * A i))) f := by
    intro i f
    have h1 : HasDerivAt (fun g : ℝ => -β * (H i - g * A i)) (β * A i) f := by
      have h0 : HasDerivAt (fun g : ℝ => g * A i) (A i) f := by
        simpa using (hasDerivAt_id f).mul_const (A i)
      have := (h0.const_sub (H i)).const_mul (-β)
      simpa [mul_comm, mul_neg, neg_mul] using this
    simpa [mul_comm] using h1.exp
  have hN : HasDerivAt (fun g : ℝ => ∑ i, B i * Real.exp (-β * (H i - g * A i)))
      (∑ i, B i * (β * A i * Real.exp (-β * H i))) 0 := by
    have h2 := HasDerivAt.sum (u := Finset.univ)
      (A := fun i => fun g : ℝ => B i * Real.exp (-β * (H i - g * A i)))
      (A' := fun i => B i * (β * A i * Real.exp (-β * (H i - 0 * A i))))
      (fun i _ => ((hexp i 0).const_mul (B i)))
    simpa [Finset.sum_fn] using h2
  have hD : HasDerivAt (partition β H A) (∑ i, β * A i * Real.exp (-β * H i)) 0 := by
    have h2 := HasDerivAt.sum (u := Finset.univ)
      (A := fun i => fun g : ℝ => Real.exp (-β * (H i - g * A i)))
      (A' := fun i => β * A i * Real.exp (-β * (H i - 0 * A i)))
      (fun i _ => hexp i 0)
    rw [show partition β H A = fun g : ℝ => ∑ i, Real.exp (-β * (H i - g * A i)) from rfl]
    simpa [Finset.sum_fn] using h2
  have hZpos : 0 < partition β H A 0 :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hq := hN.div hD (ne_of_gt hZpos)
  refine hq.congr_deriv ?_
  have hZ0 : partition β H A 0 = ∑ i, Real.exp (-β * H i) := by
    simp [partition]
  have e1 : ∑ i, B i * (β * A i * Real.exp (-β * H i))
      = β * ∑ i, A i * B i * Real.exp (-β * H i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, β * A i * Real.exp (-β * H i)
      = β * ∑ i, A i * Real.exp (-β * H i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hZ0] at hZpos
  have hZne : (∑ i, Real.exp (-β * H i)) ≠ 0 := ne_of_gt hZpos
  simp only [correlation, expect, hZ0, zero_mul, sub_zero]
  rw [e1, e2]
  field_simp

end Phys

