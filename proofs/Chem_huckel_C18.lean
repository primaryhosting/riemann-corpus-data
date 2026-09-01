/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/
noncomputable def zeta18 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

/-- The Hückel energies of the cycle `C₁₈` (in units of `β`, with `α = 0`):
`2 cos (2πk/18)` for `k = 0, …, 17`. -/
noncomputable def huckelEnergy (k : Fin 18) : ℝ := 2 * Real.cos (2 * Real.pi * k / 18)

lemma zeta18_primitive : IsPrimitiveRoot zeta18 18 :=
  Complex.isPrimitiveRoot_exp 18 (by norm_num)

lemma zeta18_pow_18 : zeta18 ^ 18 = 1 := zeta18_primitive.pow_eq_one

lemma zeta18_pow_pow_18 (k : ℕ) : (zeta18 ^ k) ^ 18 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta18_pow_18, one_pow]

lemma zeta18_pow_eq_exp (k : ℕ) :
    zeta18 ^ k = Complex.exp (((2 * Real.pi * k / 18 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta18, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ^{-k} + ζ^{k} = 2 cos (2πk/18)`. -/
lemma zeta18_pow_add_inv (k : Fin 18) :
    (zeta18 ^ (k : ℕ)) ^ 17 + zeta18 ^ (k : ℕ) = ((huckelEnergy k : ℝ) : ℂ) := by
  have h17 : (zeta18 ^ (k : ℕ)) ^ 17 = (zeta18 ^ (k : ℕ))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact zeta18_pow_pow_18 _
  rw [h17, zeta18_pow_eq_exp, ← Complex.exp_neg, huckelEnergy]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]
  ring_nf

lemma pow_mod18 {u : ℂ} (hu : u ^ 18 = 1) (x : ℕ) : u ^ (x % 18) = u ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 18]
  rw [pow_add, pow_mul, hu, one_pow, one_mul]

lemma fin18_add_pow {u : ℂ} (hu : u ^ 18 = 1) (a b : Fin 18) :
    u ^ ((a + b : Fin 18) : ℕ) = u ^ (a : ℕ) * u ^ (b : ℕ) := by
  rw [Fin.val_add, pow_mod18 hu, pow_add]

lemma fin18_sub_one (j : Fin 18) : j - 1 = j + 17 := by revert j; decide

lemma fin18_sub_ne_add (j : Fin 18) : j - 1 ≠ j + 1 := by revert j; decide

/-- The (discrete Fourier) eigenvector matrix, `F j k = ζ^{jk}`. -/
noncomputable def F18 : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.vandermonde (fun j => zeta18 ^ (j : ℕ))

lemma F18_apply (j k : Fin 18) : F18 j k = (zeta18 ^ (k : ℕ)) ^ (j : ℕ) := by
  simp [F18, Matrix.vandermonde, ← pow_mul, mul_comm]

lemma F18_isUnit : IsUnit F18 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, F18, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
  rw [sub_ne_zero]
  intro h
  exact absurd (zeta18_primitive.pow_inj j.isLt i.isLt h)
    (Fin.val_ne_of_ne (ne_of_gt (Finset.mem_Ioi.mp hj)))

/-- The eigenvalue equation `A · F = F · D`. -/
lemma adjMatrix_mul_F18 :
    (SimpleGraph.cycleGraph 18).adjMatrix ℂ * F18
      = F18 * Matrix.diagonal (fun k : Fin 18 => ((huckelEnergy k : ℝ) : ℂ)) := by
  ext j k
  have h1 : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * F18) j k
      = (((SimpleGraph.cycleGraph 18).adjMatrix ℂ) *ᵥ (fun m => F18 m k)) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, SimpleGraph.adjMatrix_mulVec_apply,
    SimpleGraph.cycleGraph_neighborFinset (n := 16), Finset.sum_pair (fin18_sub_ne_add j),
    fin18_sub_one, Matrix.mul_diagonal, F18_apply, F18_apply, F18_apply,
    fin18_add_pow (zeta18_pow_pow_18 _), fin18_add_pow (zeta18_pow_pow_18 _),
    ← zeta18_pow_add_inv k]
  norm_num
  ring

/-- The adjacency matrix of `C₁₈` is conjugate to the diagonal matrix of Hückel energies. -/
lemma adjMatrix_conj :
    (SimpleGraph.cycleGraph 18).adjMatrix ℂ
      = (F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ)
        * Matrix.diagonal (fun k : Fin 18 => ((huckelEnergy k : ℝ) : ℂ))
        * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) := by
  have hv : (F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ) = F18 := F18_isUnit.unit_spec
  have hmul : (F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ)
      * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) = 1 := Units.mul_inv _
  calc (SimpleGraph.cycleGraph 18).adjMatrix ℂ
      = (SimpleGraph.cycleGraph 18).adjMatrix ℂ
          * ((F18_isUnit.unit : Matrix (Fin 18) (Fin 18) ℂ)
            * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ)) := by rw [hmul, mul_one]
    _ = ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * F18)
          * ((F18_isUnit.unit)⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) := by rw [hv, mul_assoc]
    _ = _ := by rw [adjMatrix_mul_F18, hv]

/--
**Hückel theory for the annulene `C₁₈`.**

The characteristic polynomial of the adjacency matrix of the cycle graph `C₁₈` factors as
`∏_{k=0}^{17} (X - 2 cos (2πk/18))`, and consequently the spectrum of the adjacency matrix
is exactly the set of Hückel energies `{2 cos (2πk/18) : k = 0, …, 17}`.
-/
theorem huckel_C18 :
    ((SimpleGraph.cycleGraph 18).adjMatrix ℂ).charpoly
        = ∏ k : Fin 18, (Polynomial.X - Polynomial.C ((huckelEnergy k : ℝ) : ℂ))
      ∧ spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ)
        = Set.range (fun k : Fin 18 => ((huckelEnergy k : ℝ) : ℂ)) := by
  constructor
  · rw [adjMatrix_conj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  · rw [adjMatrix_conj, spectrum.units_conjugate, Matrix.spectrum_diagonal]

end Chem

import Mathlib

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

