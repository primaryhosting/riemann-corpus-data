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

set_option grind.warning false

namespace Phys

/-- Boltzmann weight of the microstate `i` for the Hamiltonian `E - f • A`
at inverse temperature `beta`, where `f` is the strength of the external field
conjugate to the observable `A`. -/
noncomputable def weight {ι : Type*} (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (-beta * (E i - f * A i))

/-- The partition function of the perturbed system. -/
noncomputable def partition {ι : Type*} [Fintype ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, weight beta E A f i

/-- The equilibrium (canonical ensemble) expectation value of the observable `B`
in the system perturbed by the field `f` conjugate to `A`. -/
noncomputable def avg {ι : Type*} [Fintype ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (B : ι → ℝ) : ℝ :=
  (∑ i, B i * weight beta E A f i) / partition beta E A f

lemma weight_pos {ι : Type*} (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    0 < weight beta E A f i := Real.exp_pos _

lemma partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    0 < partition beta E A f :=
  Finset.sum_pos (fun i _ => weight_pos beta E A f i) Finset.univ_nonempty

lemma hasDerivAt_weight {ι : Type*} (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun g => weight beta E A g i) (beta * A i * weight beta E A f i) f := by
  have h : HasDerivAt (fun g : ℝ => -beta * (E i - g * A i)) (beta * A i) f := by
    simpa using (((hasDerivAt_id f).mul_const (A i)).const_sub (E i)).const_mul (-beta)
  simpa [weight, mul_comm] using h.exp

/-- **Static fluctuation–dissipation theorem.**  For a classical system with a finite set
of microstates in canonical equilibrium at inverse temperature `beta`, with Hamiltonian
`E - f • A` (i.e. an external field `f` conjugate to the observable `A`), the linear
response (susceptibility) of any observable `B` to the field, `d⟨B⟩/df`, equals
`beta` times the equilibrium correlation (covariance) of `A` and `B`:
`d⟨B⟩/df = beta * (⟨A B⟩ - ⟨A⟩⟨B⟩)`. -/
theorem fluctuation_dissipation {ι : Type*} [Fintype ι] [Nonempty ι]
    (beta : ℝ) (E A B : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun g => avg beta E A g B)
      (beta * (avg beta E A f (fun i => A i * B i) - avg beta E A f A * avg beta E A f B)) f := by
  set Z : ℝ := partition beta E A f with hZdef
  have hZpos : 0 < Z := partition_pos beta E A f
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  -- derivative of the numerator
  have hN : HasDerivAt (fun g => ∑ i, B i * weight beta E A g i)
      (∑ i, B i * (beta * A i * weight beta E A f i)) f :=
    HasDerivAt.fun_sum (fun i _ => (hasDerivAt_weight beta E A f i).const_mul (B i))
  have hZ : HasDerivAt (fun g => partition beta E A g)
      (∑ i, beta * A i * weight beta E A f i) f :=
    HasDerivAt.fun_sum (fun i _ => hasDerivAt_weight beta E A f i)
  have hdiv := hN.div hZ hZne
  refine hdiv.congr_deriv ?_
  have h1 : (∑ i, B i * (beta * A i * weight beta E A f i))
      = beta * ∑ i, (A i * B i) * weight beta E A f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : (∑ i, beta * A i * weight beta E A f i)
      = beta * ∑ i, A i * weight beta E A f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1, h2]
  simp only [avg, ← hZdef]
  field_simp

end Phys

#print axioms Phys.fluctuation_dissipation

