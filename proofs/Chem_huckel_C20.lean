import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 20)

lemma w_isPrimitiveRoot : IsPrimitiveRoot w 20 := by
  have := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [w] using this

lemma w_pow_20 : w ^ 20 = 1 := w_isPrimitiveRoot.pow_eq_one

lemma w_pow_mod (a : ℕ) : w ^ a = w ^ (a % 20) := by
  conv_lhs => rw [← Nat.div_add_mod a 20]
  rw [pow_add, pow_mul, w_pow_20, one_pow, one_mul]

lemma w_pow_congr {a b : ℕ} (h : a ≡ b [MOD 20]) : w ^ a = w ^ b := by
  rw [w_pow_mod a, w_pow_mod b, h]

/-- The (unnormalized) discrete Fourier matrix of size 20. -/
noncomputable def F : Matrix (Fin 20) (Fin 20) ℂ :=
  fun j k => w ^ ((j : ℕ) * (k : ℕ))

/-- The Hückel eigenvalues of the cycle `C₂₀`. -/
noncomputable def hval (k : Fin 20) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)

lemma F_eq_vandermonde : F = Matrix.vandermonde (fun j : Fin 20 => w ^ (j : ℕ)) := by
  ext j k
  simp [F, Matrix.vandermonde, ← pow_mul]

lemma F_isUnit_det : IsUnit F.det := by
  rw [F_eq_vandermonde]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := w_isPrimitiveRoot.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- The eigenvalue identity `ω^k + ω^{19k} = 2 cos(2πk/20)`. -/
lemma w_add_inv (k : Fin 20) : w ^ (k : ℕ) + w ^ (19 * (k : ℕ)) = hval k := by
  have hwk : w ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h19 : w ^ (k : ℕ) * w ^ (19 * (k : ℕ)) = 1 := by
    rw [← pow_add, show (k : ℕ) + 19 * (k : ℕ) = 20 * (k : ℕ) by ring, pow_mul, w_pow_20,
      one_pow]
  have hne : w ^ (k : ℕ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h19
    exact zero_ne_one h19
  have hinv : w ^ (19 * (k : ℕ)) = (w ^ (k : ℕ))⁻¹ := by
    field_simp
    linear_combination h19
  have hcos : hval k = 2 * Complex.cos (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ)) := by
    rw [hval, ← Complex.ofReal_cos]
    push_cast
    ring
  rw [hinv, hwk, ← Complex.exp_neg, hcos, Complex.two_cos, neg_mul]

lemma neighbor_sum (j k : Fin 20) :
    ∑ u ∈ (cycleGraph 20).neighborFinset j, F u k = F (j - 1) k + F (j + 1) k := by
  have h : (cycleGraph 20).neighborFinset j = {j - 1, j + 1} :=
    cycleGraph_neighborFinset (n := 18) (v := j)
  have hne : (j - 1 : Fin 20) ≠ j + 1 := by revert j; decide
  rw [h, Finset.sum_pair hne]

lemma F_shift_add (j k : Fin 20) : F (j + 1) k = F j k * w ^ (k : ℕ) := by
  have hv : ((j + 1 : Fin 20) : ℕ) = ((j : ℕ) + 1) % 20 := by
    simp [Fin.val_add]
  have hcong : ((j : ℕ) + 1) % 20 * (k : ℕ) ≡ ((j : ℕ) + 1) * (k : ℕ) [MOD 20] :=
    Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  rw [F, F, hv, w_pow_congr hcong, ← pow_add]
  congr 1
  ring

lemma F_shift_sub (j k : Fin 20) : F (j - 1) k = F j k * w ^ (19 * (k : ℕ)) := by
  have hneg : (-1 : Fin 20) = 19 := rfl
  have hj : (j : Fin 20) - 1 = j + 19 := by rw [sub_eq_add_neg, hneg]
  have hv : ((j + 19 : Fin 20) : ℕ) = ((j : ℕ) + 19) % 20 := by
    simp [Fin.val_add]
  have hcong : ((j : ℕ) + 19) % 20 * (k : ℕ) ≡ ((j : ℕ) + 19) * (k : ℕ) [MOD 20] :=
    Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  rw [hj, F, F, hv, w_pow_congr hcong, ← pow_add]
  congr 1
  ring

/-- The adjacency matrix of `C₂₀` is diagonalized by the Fourier matrix. -/
lemma adj_mul_F : (cycleGraph 20).adjMatrix ℂ * F = F * Matrix.diagonal hval := by
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, neighbor_sum, F_shift_add, F_shift_sub,
    Matrix.mul_diagonal, ← mul_add, add_comm (w ^ (19 * (k : ℕ))), w_add_inv]

/-- **Hückel theory for C₂₀.**  The spectrum of the adjacency matrix of the cycle graph
`C₂₀` is exactly `{2 cos (2πk/20) : k = 0, …, 19}`. -/
theorem huckel_C20 :
    spectrum ℂ ((cycleGraph 20).adjMatrix ℂ) =
      Set.range (fun k : Fin 20 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det F).mpr F_isUnit_det
  have h1 : (cycleGraph 20).adjMatrix ℂ * (u : Matrix (Fin 20) (Fin 20) ℂ)
      = (u : Matrix (Fin 20) (Fin 20) ℂ) * Matrix.diagonal hval := by
    rw [hu]; exact adj_mul_F
  have hconj : (cycleGraph 20).adjMatrix ℂ
      = (u : Matrix (Fin 20) (Fin 20) ℂ) * Matrix.diagonal hval
        * ((u⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
    rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  rw [hconj, spectrum.units_conjugate, spectrum_diagonal]
  rfl

end Chem

