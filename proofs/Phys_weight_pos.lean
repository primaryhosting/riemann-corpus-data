/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Boltzmann weight of the microstate `i` for the perturbed Hamiltonian
`H_f = E - f • A`, at inverse temperature `β`. -/
noncomputable def weight (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (-(β * (E i - f * A i)))

/-- Partition function of the perturbed system. -/
noncomputable def partition (β : ℝ) (E A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, weight β E A f i

/-- Equilibrium (Gibbs) expectation value of the observable `g` in the perturbed system. -/
noncomputable def expect (β : ℝ) (E A : ι → ℝ) (f : ℝ) (g : ι → ℝ) : ℝ :=
  (∑ i, g i * weight β E A f i) / partition β E A f

omit [Fintype ι] in
lemma weight_pos (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : 0 < weight β E A f i :=
  Real.exp_pos _

lemma partition_pos [Nonempty ι] (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    0 < partition β E A f :=
  Finset.sum_pos (fun i _ => weight_pos β E A f i) Finset.univ_nonempty

lemma partition_ne_zero [Nonempty ι] (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    partition β E A f ≠ 0 :=
  ne_of_gt (partition_pos β E A f)

omit [Fintype ι] in
/-- The derivative in the external field `f` of a Boltzmann weight. -/
lemma hasDerivAt_weight (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun f => weight β E A f i) (β * A i * weight β E A f i) f := by
  have h : HasDerivAt (fun f : ℝ => -(β * (E i - f * A i))) (β * A i) f := by
    have : HasDerivAt (fun f : ℝ => f * A i) (1 * A i) f :=
      (hasDerivAt_id f).mul_const (A i)
    simpa using (((this.const_sub (E i)).const_mul β).neg)
  simpa [weight, mul_comm, mul_left_comm, mul_assoc] using h.exp

/-- The derivative in the external field `f` of the partition function. -/
lemma hasDerivAt_partition (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    HasDerivAt (partition β E A) (β * ∑ i, A i * weight β E A f i) f := by
  have h : HasDerivAt (fun f => ∑ i, weight β E A f i)
      (∑ i, β * A i * weight β E A f i) f :=
    HasDerivAt.fun_sum (fun i _ => hasDerivAt_weight β E A f i)
  have he : (∑ i, β * A i * weight β E A f i) = β * ∑ i, A i * weight β E A f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he] at h
  exact h

/-- The derivative in the external field `f` of the (unnormalized) moment of `g`. -/
lemma hasDerivAt_numer (β : ℝ) (E A : ι → ℝ) (g : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => ∑ i, g i * weight β E A f i)
      (β * ∑ i, g i * A i * weight β E A f i) f := by
  have h : HasDerivAt (fun f => ∑ i, g i * weight β E A f i)
      (∑ i, g i * (β * A i * weight β E A f i)) f :=
    HasDerivAt.fun_sum (fun i _ => (hasDerivAt_weight β E A f i).const_mul (g i))
  have he : (∑ i, g i * (β * A i * weight β E A f i))
      = β * ∑ i, g i * A i * weight β E A f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he] at h
  exact h

/-- The equilibrium variance of `A` equals `⟨A²⟩ - ⟨A⟩²`. -/
lemma expect_sq_sub [Nonempty ι] (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    expect β E A f (fun i => (A i - expect β E A f A) ^ 2)
      = expect β E A f (fun i => A i ^ 2) - (expect β E A f A) ^ 2 := by
  have hZ0 : partition β E A f ≠ 0 := partition_ne_zero β E A f
  set m := expect β E A f A with hm
  have hsum : ∑ i, (A i - m) ^ 2 * weight β E A f i
      = (∑ i, A i ^ 2 * weight β E A f i)
        - 2 * m * (∑ i, A i * weight β E A f i)
        + m ^ 2 * partition β E A f := by
    simp only [partition, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h1 : expect β E A f (fun i => A i ^ 2)
      = (∑ i, A i ^ 2 * weight β E A f i) / partition β E A f := rfl
  have hmv : m * partition β E A f = ∑ i, A i * weight β E A f i := by
    rw [hm, expect, div_mul_cancel₀ _ hZ0]
  show (∑ i, (A i - m) ^ 2 * weight β E A f i) / partition β E A f = _
  rw [hsum, h1, ← hmv]
  field_simp
  ring

/-- **Fluctuation–dissipation theorem** (static/classical form, Gibbs ensemble).

For a finite classical system with energies `E` at inverse temperature `β`, coupled to an
external field `f` conjugate to the observable `A` (perturbed Hamiltonian `H_f = E - f A`),
the linear response (susceptibility) of `⟨A⟩` to the field equals `β` times the
equilibrium variance of `A`, i.e. `β ⟨(A - ⟨A⟩)²⟩`: dissipation (response) is determined by
the spontaneous equilibrium fluctuations. -/
theorem fluctuation_dissipation [Nonempty ι] (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => expect β E A f A)
      (β * expect β E A f (fun i => (A i - expect β E A f A) ^ 2)) f := by
  have hZ0 : partition β E A f ≠ 0 := partition_ne_zero β E A f
  have hnum : HasDerivAt (fun f => ∑ i, A i * weight β E A f i)
      (β * ∑ i, A i ^ 2 * weight β E A f i) f := by
    have h := hasDerivAt_numer β E A A f
    have he : (∑ i, A i * A i * weight β E A f i) = ∑ i, A i ^ 2 * weight β E A f i :=
      Finset.sum_congr rfl fun i _ => by ring
    rwa [he] at h
  have hden := hasDerivAt_partition β E A f
  have hdiv := hnum.div hden hZ0
  have hval : ((β * ∑ i, A i ^ 2 * weight β E A f i) * partition β E A f
        - (∑ i, A i * weight β E A f i) * (β * ∑ i, A i * weight β E A f i))
        / partition β E A f ^ 2
      = β * expect β E A f (fun i => (A i - expect β E A f A) ^ 2) := by
    rw [expect_sq_sub]
    have h1 : expect β E A f (fun i => A i ^ 2)
        = (∑ i, A i ^ 2 * weight β E A f i) / partition β E A f := rfl
    have h2 : expect β E A f A = (∑ i, A i * weight β E A f i) / partition β E A f := rfl
    rw [h1, h2]
    field_simp
  rw [← hval]
  exact hdiv

/-- Consequence of the fluctuation-dissipation theorem: at positive temperature the
susceptibility `d⟨A⟩/df` is nonnegative, since it is `β` times a variance. -/
theorem susceptibility_nonneg [Nonempty ι] {β : ℝ} (hβ : 0 ≤ β) (E A : ι → ℝ) (f : ℝ) :
    0 ≤ deriv (fun f => expect β E A f A) f := by
  rw [(fluctuation_dissipation β E A f).deriv]
  refine mul_nonneg hβ (div_nonneg ?_ (le_of_lt (partition_pos β E A f)))
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (le_of_lt (weight_pos β E A f i))

end Phys

