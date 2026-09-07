/-
  Brockian/Fin5InnerProduct.lean

  Hermitian (sesquilinear) product on the D₅ permutation representation
  `VertexSpace = Fin 5 → ℂ`, and orthogonality of the cyclic Fourier eigenmodes
  from `Brockian.D5Isotypic`.

  Honest scope (this file proves, and only proves):
    * Hermitian product
        `⟪f, g⟫ = ∑_x star(f x) · g x`
      with sesquilinearity (conj-linear left, linear right), conjugate symmetry,
      and positive-definiteness (`⟪f,f⟫ = 0 ↔ f = 0`).
    * Conjugation of fifth roots: `star(ω^a) = ω^{-a}`.
    * Pairwise eigenmode formula:
        `⟪vⱼ, vₗ⟫ = 5 · δⱼₗ`
      (hence `j ≠ ℓ → ⟪vⱼ, vₗ⟫ = 0`, and `⟪vⱼ, vⱼ⟫ = 5`).

  Not claimed:
    * Full D₅ real-irrep isotypic orthogonality (2-dim blocks).
    * Any RH / ζ-spectral statement.  No new axioms.

  Verification target (spec §2A): AXLE @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.D5Isotypic
import Brockian.D5Representation

open BigOperators
open Complex
open Brockian.D5Representation
open Brockian.D5Isotypic

namespace Brockian.Fin5InnerProduct

local notation "ω" => omega
/-- Complex conjugation as a ring endomorphism (physics first-slot convention). -/
local notation "starC" => (starRingEnd ℂ)

/-! ### Hermitian product on `VertexSpace` -/

/-- Hermitian product on vertex functions:
`⟪f, g⟫ = ∑_x star(f x) · g x` (physics convention: conj-linear in the first slot). -/
noncomputable def hermInner (f g : VertexSpace) : ℂ :=
  ∑ x : Fin 5, starC (f x) * g x

local notation "⟪" f ", " g "⟫" => hermInner f g

@[simp] theorem hermInner_apply (f g : VertexSpace) :
    ⟪f, g⟫ = ∑ x : Fin 5, starC (f x) * g x :=
  rfl

/-- Right-linearity: `⟪f, g₁ + g₂⟫ = ⟪f, g₁⟫ + ⟪f, g₂⟫`. -/
theorem hermInner_add_right (f g₁ g₂ : VertexSpace) :
    ⟪f, g₁ + g₂⟫ = ⟪f, g₁⟫ + ⟪f, g₂⟫ := by
  simp only [hermInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Left-additivity: `⟪f₁ + f₂, g⟫ = ⟪f₁, g⟫ + ⟪f₂, g⟫`. -/
theorem hermInner_add_left (f₁ f₂ g : VertexSpace) :
    ⟪f₁ + f₂, g⟫ = ⟪f₁, g⟫ + ⟪f₂, g⟫ := by
  simp only [hermInner, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/-- Right ℂ-homogeneity: `⟪f, c • g⟫ = c · ⟪f, g⟫`. -/
theorem hermInner_smul_right (c : ℂ) (f g : VertexSpace) :
    ⟪f, c • g⟫ = c * ⟪f, g⟫ := by
  simp only [hermInner, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ x : Fin 5,
      starC (f x) * (c * g x) = c * (starC (f x) * g x) := by
    intro x; ring
  simp_rw [hterm]
  exact (Finset.mul_sum (Finset.univ : Finset (Fin 5))
    (fun x => starC (f x) * g x) c).symm

/-- Left conjugate-homogeneity: `⟪c • f, g⟫ = star(c) · ⟪f, g⟫`. -/
theorem hermInner_smul_left (c : ℂ) (f g : VertexSpace) :
    ⟪c • f, g⟫ = starC c * ⟪f, g⟫ := by
  simp only [hermInner, Pi.smul_apply, smul_eq_mul, map_mul]
  have hterm : ∀ x : Fin 5,
      (starC c * starC (f x)) * g x = starC c * (starC (f x) * g x) := by
    intro x; ring
  simp_rw [hterm]
  exact (Finset.mul_sum (Finset.univ : Finset (Fin 5))
    (fun x => starC (f x) * g x) (starC c)).symm

/-- Conjugate symmetry: `⟪f, g⟫ = star(⟪g, f⟫)`. -/
theorem hermInner_conj_symm (f g : VertexSpace) :
    ⟪f, g⟫ = starC ⟪g, f⟫ := by
  simp only [hermInner]
  -- `star(∑ ·) = ∑ star(·)` then rearrange factors
  rw [map_sum (starRingEnd ℂ)]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- Goal: `star(f x) * g x = star(star(g x) * f x)`.
  have h : starC (starC (g x) * f x) = starC (f x) * g x := by
    rw [map_mul]
    -- `star(star g) * star f`
    have hg : starC (starC (g x)) = g x := by
      simpa using (star_star (g x) : star (star (g x)) = g x)
    rw [hg, mul_comm]
  exact h.symm

/-- Quadratic form equals sum of squared moduli:
`⟪f, f⟫ = ∑_x ‖f x‖²` (as a complex with zero imaginary part). -/
theorem hermInner_self (f : VertexSpace) :
    ⟪f, f⟫ = ∑ x : Fin 5, (↑(Complex.normSq (f x)) : ℂ) := by
  simp only [hermInner]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- `star z * z = z * star z = ↑(normSq z)`
  rw [mul_comm]
  exact Complex.mul_conj (f x)

/-- Positive-definiteness: `⟪f, f⟫ = 0` iff `f = 0`. -/
theorem hermInner_self_eq_zero_iff (f : VertexSpace) :
    ⟪f, f⟫ = 0 ↔ f = 0 := by
  constructor
  · intro h
    -- From `∑ ↑(normSq) = 0` recover `∑ normSq = 0`, then each term vanishes.
    have hsumC : ∑ y : Fin 5, (↑(Complex.normSq (f y)) : ℂ) = 0 := by
      rwa [hermInner_self] at h
    have hsum : ∑ y : Fin 5, Complex.normSq (f y) = 0 := by
      have hlift :
          (↑(∑ y : Fin 5, Complex.normSq (f y)) : ℂ) =
            ∑ y : Fin 5, (↑(Complex.normSq (f y)) : ℂ) :=
        map_sum (algebraMap ℝ ℂ) (fun y => Complex.normSq (f y)) Finset.univ
      have : (↑(∑ y : Fin 5, Complex.normSq (f y)) : ℂ) = 0 := by
        rw [hlift, hsumC]
      exact (Complex.ofReal_eq_zero).1 this
    funext x
    have hx : Complex.normSq (f x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y (_ : y ∈ (Finset.univ : Finset (Fin 5))) =>
          Complex.normSq_nonneg (f y))).1 hsum x (Finset.mem_univ x)
    simpa using (Complex.normSq_eq_zero.1 hx)
  · intro hf
    rw [hf]
    simp [hermInner]

/-! ### Conjugation of powers of `ω` -/

/-- The primitive fifth root lies on the unit circle. -/
theorem norm_omega : ‖ω‖ = 1 := by
  -- `ω = exp(2π i / 5) = exp((2π/5) · i)`
  unfold omega
  have h : (2 * Real.pi * I / 5 : ℂ) = (↑(2 * Real.pi / 5) : ℂ) * I := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  rw [h, norm_exp_ofReal_mul_I]

/-- `star(ω) = ω⁻¹`. -/
theorem conj_omega : starC ω = ω⁻¹ :=
  (Complex.inv_eq_conj norm_omega).symm

/-- Conjugation of finite powers: `star(ω^n) = ω⁻ⁿ`. -/
theorem conj_omega_pow (n : ℕ) : starC (ω ^ n) = ω⁻¹ ^ n := by
  rw [map_pow, conj_omega]

/-- On `Fin 5` exponents: `star(ω^a) = ω^{-a}`. -/
theorem conj_omegaPow (a : Fin 5) : starC (omegaPow a) = omegaPow (-a) := by
  -- `star(ω^{a.val}) = (ω⁻¹)^{a.val} = (ω^{a.val})⁻¹ = omegaPow (-a)`
  rw [omegaPow_neg, omegaPow, conj_omega_pow, ← inv_pow]

/-! ### Eigenmode orthogonality -/

/-- **Pairwise eigenmode formula.**
`⟪vⱼ, vₗ⟫ = 5` if `j = ℓ`, else `0`. -/
theorem hermInner_eigenmode (j ℓ : Fin 5) :
    ⟪eigenmode j, eigenmode ℓ⟫ = if j = ℓ then (5 : ℂ) else 0 := by
  simp only [hermInner, eigenmode_apply]
  -- rewrite each star(ω^{j x}) via conj_omegaPow
  have hterm : ∀ x : Fin 5,
      starC (omegaPow (j * x)) * omegaPow (ℓ * x) =
        omegaPow ((ℓ - j) * x) := by
    intro x
    rw [conj_omegaPow, ← omegaPow_add]
    congr 1
    calc
      -(j * x) + ℓ * x = ℓ * x + -(j * x) := by abel
      _ = ℓ * x + (-j) * x := by rw [neg_mul]
      _ = (ℓ + -j) * x := by rw [← add_mul]
      _ = (ℓ - j) * x := by rw [← sub_eq_add_neg]
  simp_rw [hterm]
  -- geometric sum: `∑_x ω^{(ℓ−j)x} = 5` iff `ℓ = j`
  rw [sum_omegaPow (ℓ - j)]
  by_cases hjl : j = ℓ
  · subst hjl
    simp only [sub_self, ↓reduceIte]
  · have hne : ℓ - j ≠ 0 := fun h => hjl (sub_eq_zero.mp h).symm
    simp only [hne, hjl, ↓reduceIte]

/-- Eigenmodes of distinct frequencies are orthogonal. -/
theorem eigenmode_orthogonal {j ℓ : Fin 5} (h : j ≠ ℓ) :
    ⟪eigenmode j, eigenmode ℓ⟫ = 0 := by
  rw [hermInner_eigenmode, if_neg h]

/-- Self-inner product of every eigenmode is `5`. -/
theorem hermInner_eigenmode_self (j : Fin 5) :
    ⟪eigenmode j, eigenmode j⟫ = (5 : ℂ) := by
  rw [hermInner_eigenmode, if_pos rfl]

/-- The constant mode (frequency 0) has `⟪v₀, v₀⟫ = 5`. -/
theorem hermInner_eigenmode_zero :
    ⟪eigenmode 0, eigenmode 0⟫ = (5 : ℂ) :=
  hermInner_eigenmode_self 0

end Brockian.Fin5InnerProduct
