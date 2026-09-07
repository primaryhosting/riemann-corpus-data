/-
  Brockian/D5FourierInversion.lean

  Full Fourier inversion and isotypic projector algebra on *all* of
  `VertexSpace = Fin 5 → ℂ`, extending the eigenmode-only results of
  `Brockian.D5Isotypic`.

  Honest scope (this file proves, and only proves):
    * Fourier coefficients `ĉⱼ(f) = (1/5) ∑_x f(x) ω^{-j x}`.
    * Projector–mode relation: `Pⱼ f = ĉⱼ(f) • vⱼ` for every `f`.
    * Fourier inversion: `f = ∑_j ĉⱼ(f) • vⱼ`.
    * Resolution of the identity: `∑_j Pⱼ f = f`.
    * Full-space idempotence: `Pⱼ (Pⱼ f) = Pⱼ f`.
    * Full-space orthogonality: `j ≠ ℓ → Pⱼ (Pₗ f) = 0`.

  Uses character orthogonality / geometric sums from `D5Isotypic`; does not
  rewrite that module.  No RH / spectral claim about ζ.  No new axioms.

  Verification target (spec §2A): AXLE @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.D5Isotypic
import Brockian.D5Representation

open BigOperators
open DihedralGroup
open Complex
open Brockian.D5Representation
open Brockian.D5Isotypic

namespace Brockian.D5FourierInversion

/-! ### Fourier coefficients -/

/-- Cyclic Fourier coefficient of frequency `j`:
`ĉⱼ(f) = (1/5) ∑_x f(x) · ω^{-j x}`. -/
noncomputable def fourierCoeff (j : Fin 5) (f : VertexSpace) : ℂ :=
  (5 : ℂ)⁻¹ * ∑ x : Fin 5, f x * omegaPow (-(j * x))

theorem fourierCoeff_apply (j : Fin 5) (f : VertexSpace) :
    fourierCoeff j f =
      (5 : ℂ)⁻¹ * ∑ x : Fin 5, f x * omegaPow (-(j * x)) := rfl

/-- Homogeneity of Fourier coefficients. -/
theorem fourierCoeff_smul (j : Fin 5) (c : ℂ) (f : VertexSpace) :
    fourierCoeff j (c • f) = c * fourierCoeff j f := by
  simp only [fourierCoeff, Pi.smul_apply, smul_eq_mul]
  -- `(5)⁻¹ * ∑ ((c * f x) * ω) = c * ((5)⁻¹ * ∑ f x * ω)`
  have hsum :
      ∑ x : Fin 5, (c * f x) * omegaPow (-(j * x)) =
        c * ∑ x : Fin 5, f x * omegaPow (-(j * x)) := by
    simp_rw [mul_assoc]
    exact (Finset.mul_sum (Finset.univ : Finset (Fin 5))
      (fun x => f x * omegaPow (-(j * x))) c).symm
  rw [hsum]
  ring

/-- Additivity of Fourier coefficients. -/
theorem fourierCoeff_add (j : Fin 5) (f g : VertexSpace) :
    fourierCoeff j (f + g) = fourierCoeff j f + fourierCoeff j g := by
  simp only [fourierCoeff, Pi.add_apply]
  have hsum :
      ∑ x : Fin 5, (f x + g x) * omegaPow (-(j * x)) =
        ∑ x : Fin 5, f x * omegaPow (-(j * x)) +
          ∑ x : Fin 5, g x * omegaPow (-(j * x)) := by
    simp_rw [add_mul]
    exact Finset.sum_add_distrib
  rw [hsum, mul_add]

/-! ### Projector = coefficient · eigenmode (pointwise) -/

/-- Reindex helper: summing `g (x − k)` over all `k` is summing `g` over all vertices. -/
private theorem sum_sub_eq_sum (x : Fin 5) (g : Fin 5 → ℂ) :
    ∑ k : Fin 5, g (x - k) = ∑ y : Fin 5, g y :=
  (Equiv.subLeft x).sum_comp g

/-- **Projector–Fourier relation.**  For every vertex function,
`Pⱼ f = ĉⱼ(f) · vⱼ`. -/
theorem isotypicProjector_eq_fourierCoeff_smul (j : Fin 5) (f : VertexSpace) :
    isotypicProjector j f = fourierCoeff j f • eigenmode j := by
  funext x
  simp only [isotypicProjector_apply, fourierCoeff, Pi.smul_apply, smul_eq_mul,
    eigenmode_apply]
  -- Reindex `k ↦ y := x − k`: `ω^{j k} f(x−k) = ω^{j(x−y)} f(y)`.
  have hreindex :
      ∑ k : Fin 5, omegaPow (j * k) * f (x - k) =
        ∑ y : Fin 5, omegaPow (j * (x - y)) * f y := by
    have hterm : ∀ k : Fin 5,
        omegaPow (j * k) * f (x - k) =
          omegaPow (j * (x - (x - k))) * f (x - k) := by
      intro k
      have hxk : x - (x - k) = k := by abel
      rw [hxk]
    simp_rw [hterm]
    exact sum_sub_eq_sum x (fun y => omegaPow (j * (x - y)) * f y)
  have hfactor :
      ∑ y : Fin 5, omegaPow (j * (x - y)) * f y =
        omegaPow (j * x) * ∑ y : Fin 5, f y * omegaPow (-(j * y)) := by
    have hterm : ∀ y : Fin 5,
        omegaPow (j * (x - y)) * f y =
          omegaPow (j * x) * (f y * omegaPow (-(j * y))) := by
      intro y
      have hidx : j * (x - y) = j * x + -(j * y) := by
        rw [sub_eq_add_neg, mul_add, mul_neg]
      have hpow :
          omegaPow (j * (x - y)) =
            omegaPow (j * x) * omegaPow (-(j * y)) := by
        rw [hidx, omegaPow_add]
      rw [hpow]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
  rw [hreindex, hfactor]
  ring

/-! ### Resolution of the identity / Fourier inversion -/

/-- Geometric sum over frequencies: `∑_j ω^{j k} = 5` if `k = 0`, else `0`. -/
private theorem sum_omegaPow_freq (k : Fin 5) :
    ∑ j : Fin 5, omegaPow (j * k) = if k = 0 then (5 : ℂ) else 0 := by
  simpa [mul_comm] using sum_omegaPow k

/-- **Resolution of the identity.**  The cyclic isotypic projectors sum to `id`
on all of `VertexSpace`: `∑_j Pⱼ f = f`. -/
theorem sum_isotypicProjectors (f : VertexSpace) :
    ∑ j : Fin 5, isotypicProjector j f = f := by
  funext x
  simp only [Finset.sum_apply, isotypicProjector_apply]
  have hswap :
      ∑ j : Fin 5, (5 : ℂ)⁻¹ * ∑ k : Fin 5, omegaPow (j * k) * f (x - k) =
        (5 : ℂ)⁻¹ * ∑ k : Fin 5, f (x - k) * ∑ j : Fin 5, omegaPow (j * k) := by
    simp_rw [← Finset.mul_sum]
    congr 1
    have hcomm :
        ∑ j : Fin 5, ∑ k : Fin 5, omegaPow (j * k) * f (x - k) =
          ∑ k : Fin 5, ∑ j : Fin 5, omegaPow (j * k) * f (x - k) :=
      Finset.sum_comm
    rw [hcomm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hfac :
        ∑ j : Fin 5, omegaPow (j * k) * f (x - k) =
          f (x - k) * ∑ j : Fin 5, omegaPow (j * k) := by
      simp_rw [mul_comm (omegaPow _) (f (x - k))]
      exact (Finset.mul_sum _ _ _).symm
    exact hfac
  rw [hswap]
  have hsumk :
      ∑ k : Fin 5, f (x - k) * ∑ j : Fin 5, omegaPow (j * k) =
        f (x - 0) * (5 : ℂ) := by
    have hform :
        ∑ k : Fin 5, f (x - k) * ∑ j : Fin 5, omegaPow (j * k) =
          ∑ k : Fin 5, f (x - k) * (if k = 0 then (5 : ℂ) else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_omegaPow_freq k]
    rw [hform]
    classical
    rw [Finset.sum_eq_single (0 : Fin 5)]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  rw [hsumk]
  simp only [sub_zero]
  field_simp

/-- **Fourier inversion on `VertexSpace`.**
`f = ∑_j ĉⱼ(f) · vⱼ`. -/
theorem fourier_inversion (f : VertexSpace) :
    ∑ j : Fin 5, fourierCoeff j f • eigenmode j = f := by
  have hproj :
      ∑ j : Fin 5, fourierCoeff j f • eigenmode j =
        ∑ j : Fin 5, isotypicProjector j f := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (isotypicProjector_eq_fourierCoeff_smul j f).symm
  rw [hproj, sum_isotypicProjectors]

/-! ### Full-space projector algebra -/

/-- Additivity of the isotypic projector (extends `isotypicProjector_smul`). -/
theorem isotypicProjector_add (j : Fin 5) (f g : VertexSpace) :
    isotypicProjector j (f + g) = isotypicProjector j f + isotypicProjector j g := by
  rw [isotypicProjector_eq_fourierCoeff_smul, isotypicProjector_eq_fourierCoeff_smul,
    isotypicProjector_eq_fourierCoeff_smul, fourierCoeff_add, add_smul]

/-- **Idempotence on all of `VertexSpace`:** `Pⱼ ∘ Pⱼ = Pⱼ`. -/
theorem isotypicProjector_idempotent (j : Fin 5) (f : VertexSpace) :
    isotypicProjector j (isotypicProjector j f) = isotypicProjector j f := by
  rw [isotypicProjector_eq_fourierCoeff_smul j f]
  rw [isotypicProjector_smul, isotypicProjector_eigenmode_self]

/-- **Orthogonality on all of `VertexSpace`:** distinct projectors annihilate. -/
theorem isotypicProjector_orthogonal {j ℓ : Fin 5} (h : j ≠ ℓ) (f : VertexSpace) :
    isotypicProjector j (isotypicProjector ℓ f) = 0 := by
  rw [isotypicProjector_eq_fourierCoeff_smul ℓ f]
  rw [isotypicProjector_smul, isotypicProjector_eigenmode_of_ne h, smul_zero]

/-- Fourier coefficient of an eigenmode: `ĉⱼ(vₗ) = δⱼₗ`. -/
theorem fourierCoeff_eigenmode (j ℓ : Fin 5) :
    fourierCoeff j (eigenmode ℓ) = if j = ℓ then (1 : ℂ) else 0 := by
  simp only [fourierCoeff, eigenmode_apply]
  have hterm : ∀ x : Fin 5,
      omegaPow (ℓ * x) * omegaPow (-(j * x)) = omegaPow ((ℓ - j) * x) := by
    intro x
    rw [← omegaPow_add]
    congr 1
    calc
      ℓ * x + -(j * x) = ℓ * x + (-j) * x := by rw [neg_mul]
      _ = (ℓ + -j) * x := by rw [← add_mul]
      _ = (ℓ - j) * x := by rw [← sub_eq_add_neg]
  simp_rw [hterm]
  -- `(5)⁻¹ * ∑_x ω^{(ℓ−j) x} = if ℓ = j then 1 else 0`, flip equality test.
  have hchar := character_orthogonality ℓ j
  rw [hchar]
  simp [eq_comm]

end Brockian.D5FourierInversion
