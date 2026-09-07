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

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `±1` mod `7`. -/
def C7 : Matrix (ZMod 7) (ZMod 7) ℝ :=
  Matrix.of fun i j => if i - j = 1 ∨ i - j = -1 then (1 : ℝ) else 0

/-- The `k`-th Hückel eigenvalue of `C₇`. -/
noncomputable def C7eigen (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 7)

/-- The discrete Fourier ("Bloch wave") matrix over `ℂ`: `F7 i k = e (i * k)` where `e` is the
standard additive character of `ZMod 7`. -/
noncomputable def F7 : Matrix (ZMod 7) (ZMod 7) ℂ :=
  Matrix.of fun i k => ZMod.stdAddChar (i * k)

/-- The inverse of `F7`. -/
noncomputable def G7 : Matrix (ZMod 7) (ZMod 7) ℂ :=
  Matrix.of fun k j => (7 : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j))

private lemma stdAddChar_sum (t : ZMod 7) :
    ∑ i : ZMod 7, ZMod.stdAddChar (t * i) = if t = 0 then (7 : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
    norm_num
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 7 h)

private lemma char_add_neg (n : ℕ) :
    ZMod.stdAddChar ((n : ZMod 7)) + ZMod.stdAddChar (-(n : ZMod 7)) = ((C7eigen n : ℝ) : ℂ) := by
  have h1 : ((n : ZMod 7)) = ((n : ℤ) : ZMod 7) := by push_cast; ring
  rw [C7eigen, h1, ← Int.cast_neg, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  rw [Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  rw [Complex.two_cos]
  ring_nf

private lemma F7_mul_G7 : F7 * G7 = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [F7, G7, Matrix.of_apply]
  have key : ∀ k : ZMod 7, ZMod.stdAddChar (i * k) * ((7 : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j)))
      = (7 : ℂ)⁻¹ * ZMod.stdAddChar ((i - j) * k) := by
    intro k
    rw [← mul_assoc, mul_comm (ZMod.stdAddChar (i * k)) ((7 : ℂ)⁻¹), mul_assoc,
      ← AddChar.map_add_eq_mul]
    ring_nf
  simp only [key, ← Finset.mul_sum, stdAddChar_sum, sub_eq_zero]
  by_cases h : i = j
  · rw [h]
    simp [Matrix.one_apply_eq]
  · simp [h, Matrix.one_apply_ne h]

private lemma G7_mul_F7 : G7 * F7 = 1 := by
  rw [mul_eq_one_comm]
  exact F7_mul_G7

/-- The adjacency matrix of `C₇`, viewed over `ℂ`, is diagonalized by the Fourier matrix `F7`. -/
private lemma C7_mul_F7 :
    (C7.map (algebraMap ℝ ℂ)) * F7 = F7 * Matrix.diagonal (fun k : ZMod 7 =>
      (algebraMap ℝ ℂ) (C7eigen k.val)) := by
  have hcond : ∀ i j : ZMod 7, ((i - j = 1 ∨ i - j = -1) ↔ (j = i - 1 ∨ j = i + 1)) := by decide
  have hne : ∀ i : ZMod 7, (i - 1 : ZMod 7) ≠ i + 1 := by decide
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hsum : ∀ j : ZMod 7, (C7.map (algebraMap ℝ ℂ)) i j * F7 j k
      = (if j = i - 1 then ZMod.stdAddChar (j * k) else 0)
        + (if j = i + 1 then ZMod.stdAddChar (j * k) else 0) := by
    intro j
    simp only [C7, F7, Matrix.map_apply, Matrix.of_apply, hcond i j]
    by_cases h1 : j = i - 1
    · have h2 : j ≠ i + 1 := by rw [h1]; exact hne i
      simp [h1, hne i]
    · by_cases h2 : j = i + 1 <;> simp [h1, h2, Ne.symm (hne i)]
  rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [F7, Matrix.of_apply, Complex.coe_algebraMap]
  have hk : ((k.val : ZMod 7)) = k := by simp [ZMod.natCast_val, ZMod.cast_id]
  have e1 : ((i - 1) * k : ZMod 7) = i * k + (-(k.val : ZMod 7)) := by rw [hk]; ring
  have e2 : ((i + 1) * k : ZMod 7) = i * k + ((k.val : ZMod 7)) := by rw [hk]; ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add, add_comm
    (ZMod.stdAddChar (-(k.val : ZMod 7))), char_add_neg]

private lemma charpoly_C7_complex :
    (C7.map (algebraMap ℝ ℂ)).charpoly =
      ∏ k : ZMod 7, (X - C ((algebraMap ℝ ℂ) (C7eigen k.val))) := by
  set D : Matrix (ZMod 7) (ZMod 7) ℂ :=
    Matrix.diagonal (fun k : ZMod 7 => (algebraMap ℝ ℂ) (C7eigen k.val)) with hD
  have hfac : C7.map (algebraMap ℝ ℂ) = F7 * (D * G7) := by
    rw [← mul_assoc, ← C7_mul_F7, mul_assoc, F7_mul_G7, mul_one]
  rw [hfac, Matrix.charpoly_mul_comm, mul_assoc, G7_mul_F7, mul_one, hD,
    Matrix.charpoly_diagonal]

private lemma prod_zmod_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ k : ZMod 7, f k.val = ∏ n ∈ Finset.range 7, f n := by
  refine Finset.prod_nbij' (fun k => k.val) (fun n => (n : ZMod 7)) ?_ ?_ ?_ ?_ ?_
  · intro k _
    simpa [Finset.mem_range] using ZMod.val_lt k
  · intro n _
    exact Finset.mem_univ _
  · intro k _
    simp [ZMod.natCast_val, ZMod.cast_id]
  · intro n hn
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro k _
    rfl

/-- **Hückel theory for `C₇`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₇` is `∏_{k=0}^{6} (X - 2 cos (2πk/7))`, i.e. the adjacency eigenvalues of `C₇`,
counted with multiplicity, are `2 cos (2πk/7)` for `k = 0, …, 6`. -/
theorem huckel_C7 :
    C7.charpoly = ∏ k ∈ Finset.range 7, (X - C (2 * Real.cos (2 * Real.pi * k / 7))) := by
  have hinj : Function.Injective (algebraMap ℝ ℂ) := (algebraMap ℝ ℂ).injective
  refine Polynomial.map_injective (algebraMap ℝ ℂ) hinj ?_
  rw [← Matrix.charpoly_map, charpoly_C7_complex, Polynomial.map_prod]
  rw [prod_zmod_eq_prod_range (fun n => X - C ((algebraMap ℝ ℂ) (C7eigen n)))]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  simp [C7eigen, Polynomial.map_sub]

/-- The spectrum (set of eigenvalues) of the adjacency matrix of `C₇` is exactly the set of
numbers `2 cos (2πk/7)` for `k = 0, …, 6`. -/
theorem spectrum_C7 :
    spectrum ℝ C7 = {x : ℝ | ∃ k ∈ Finset.range 7, x = 2 * Real.cos (2 * Real.pi * k / 7)} := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C7, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

end Chem

