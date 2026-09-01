import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- **Jarzynski equality** (finite / classical deterministic setting).

Setting: a finite state space `X`, inverse temperature `β > 0`, an initial Hamiltonian `H₀`
and a final Hamiltonian `H₁`.  The driving protocol is a deterministic, phase-space
volume preserving (here: bijective, i.e. counting-measure preserving) evolution
`evol : X ≃ X`, and the work performed along the trajectory starting at `x` is
`W x = H₁ (evol x) - H₀ x`.

The system starts in the canonical (Gibbs) equilibrium distribution
`p x = exp (-β * H₀ x) / Z₀`, where `Z₀`, `Z₁` are the partition functions of the
initial and final Hamiltonians and `Fᵢ = -(log Zᵢ)/β` the corresponding free energies.

Conclusion: the exponential average of the work equals the exponential of the
free-energy difference,
`⟨exp (-β W)⟩ = exp (-β ΔF)` with `ΔF = F₁ - F₀`. -/
theorem jarzynski_equality
    {X : Type*} [Fintype X] [Nonempty X]
    (β : ℝ) (hβ : 0 < β)
    (H₀ H₁ : X → ℝ) (evol : X ≃ X)
    (W : X → ℝ) (hW : ∀ x, W x = H₁ (evol x) - H₀ x)
    (Z₀ Z₁ : ℝ)
    (hZ₀ : Z₀ = ∑ x, Real.exp (-β * H₀ x))
    (hZ₁ : Z₁ = ∑ x, Real.exp (-β * H₁ x))
    (F₀ F₁ : ℝ) (hF₀ : F₀ = -(Real.log Z₀) / β) (hF₁ : F₁ = -(Real.log Z₁) / β) :
    ∑ x, (Real.exp (-β * H₀ x) / Z₀) * Real.exp (-β * W x)
      = Real.exp (-β * (F₁ - F₀)) := by
  have hβ' : β ≠ 0 := ne_of_gt hβ
  have hZ₀pos : 0 < Z₀ := by
    rw [hZ₀]
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ₁pos : 0 < Z₁ := by
    rw [hZ₁]
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hlhs : ∑ x, (Real.exp (-β * H₀ x) / Z₀) * Real.exp (-β * W x)
      = (∑ x, Real.exp (-β * H₁ (evol x))) / Z₀ := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hW x, div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  have hperm : (∑ x, Real.exp (-β * H₁ (evol x))) = Z₁ := by
    rw [hZ₁]
    exact Equiv.sum_comp evol (fun y => Real.exp (-β * H₁ y))
  rw [hlhs, hperm, hF₀, hF₁]
  have hexp : -β * (-(Real.log Z₁) / β - -(Real.log Z₀) / β)
      = Real.log Z₁ - Real.log Z₀ := by
    field_simp; ring
  rw [hexp, Real.exp_sub, Real.exp_log hZ₁pos, Real.exp_log hZ₀pos]

end Phys

