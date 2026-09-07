/-
  Brockian/D5LaplacianModes.lean

  Cycle adjacency / Laplacian diagonalization on the D₅ permutation
  representation `VertexSpace = Fin 5 → ℂ`, using the Fourier eigenmodes
  already built in `Brockian.D5Isotypic`.

  Honest scope (this file proves, and only proves):
    * Cycle adjacency operator
        `(A f)(x) = f(x − 1) + f(x + 1)`
      equivalently as the sum of rotation pullbacks
        `A f = r₁ • f + r₋₁ • f`.
    * Eigenrelation on Fourier modes:
        `A vⱼ = (ωʲ + ω⁻ʲ) • vⱼ`
      and the cosine form
        `ωʲ + ω⁻ʲ = 2 cos(2π · j.val / 5)`.
    * Graph Laplacian of the 2-regular 5-cycle:
        `L = 2I − A`, with
        `L vⱼ = (2 − 2 cos(2π · j.val / 5)) • vⱼ`.
    * Cyclic isotypic projectors preserve eigenmodes of `A` / `L`
      (they act as δ on the Fourier basis, which already diagonalizes both).

  Not claimed:
    * Full matrix diagonalization of an arbitrary vector (Fourier inversion).
    * Any RH / ζ-spectral statement.  No new axioms.

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

namespace Brockian.D5LaplacianModes

local notation "ω" => omega

/-! ### Cycle adjacency on `VertexSpace` -/

/-- Adjacency operator of the 5-cycle: each vertex has neighbours `x±1`. -/
noncomputable def adjacency (f : VertexSpace) : VertexSpace :=
  fun x => f (x - 1) + f (x + 1)

theorem adjacency_apply (f : VertexSpace) (x : Fin 5) :
    adjacency f x = f (x - 1) + f (x + 1) :=
  rfl

/-- Adjacency is the sum of the two generator rotation pullbacks. -/
theorem adjacency_eq_pullbacks (f : VertexSpace) :
    adjacency f = d5Pull (r (1 : Fin 5)) f + d5Pull (r (-1 : Fin 5)) f := by
  ext x
  have hx : (x + 1 : Fin 5) = x - (-1) := by
    simp [sub_eq_add_neg]
  simp only [adjacency, Pi.add_apply, d5Pull_r_apply, hx]

/-- Adjacency is linear (ℂ-homogeneous + additive). -/
theorem adjacency_add (f g : VertexSpace) :
    adjacency (f + g) = adjacency f + adjacency g := by
  ext x
  simp [adjacency, add_add_add_comm]

theorem adjacency_smul (c : ℂ) (f : VertexSpace) :
    adjacency (c • f) = c • adjacency f := by
  ext x
  simp [adjacency, mul_add]

/-- Linear map form of the cycle adjacency. -/
noncomputable def adjacencyLinear : VertexSpace →ₗ[ℂ] VertexSpace where
  toFun := adjacency
  map_add' := adjacency_add
  map_smul' := by
    intro c f
    simpa using adjacency_smul c f

@[simp] theorem adjacencyLinear_apply (f : VertexSpace) :
    adjacencyLinear f = adjacency f :=
  rfl

/-! ### Adjacency eigenvalues of Fourier modes -/

/-- **Mode eigenrelation (root form).**
`A vⱼ = (ωʲ + ω⁻ʲ) • vⱼ`, via the pullback characters
`r₁ • vⱼ = ω⁻ʲ • vⱼ` and `r₋₁ • vⱼ = ωʲ • vⱼ`. -/
theorem adjacency_eigenmode (j : Fin 5) :
    adjacency (eigenmode j) =
      (omegaPow j + omegaPow (-j)) • eigenmode j := by
  rw [adjacency_eq_pullbacks, d5Pull_r_eigenmode j 1, d5Pull_r_eigenmode j (-1)]
  -- `j * 1 = j`, `j * (-1) = -j`, so characters are `ω^{-j}` and `ω^{j}`.
  have h1 : omegaPow (-(j * (1 : Fin 5))) = omegaPow (-j) := by
    simp [mul_one]
  have hneg : omegaPow (-(j * (-1 : Fin 5))) = omegaPow j := by
    simp [mul_neg, neg_neg]
  rw [h1, hneg, ← add_smul]
  congr 1
  ac_rfl

/-- `ω^{j.val} = exp(2π i · j.val / 5)`. -/
theorem omegaPow_eq_exp (j : Fin 5) :
    omegaPow j = exp ((j.val : ℂ) * (2 * Real.pi * I / 5)) := by
  -- `exp (n · z) = (exp z)^n` with `z = 2πi/5`
  simpa [omegaPow, omega] using (exp_nat_mul (2 * Real.pi * I / 5) j.val).symm

/-- Same phase written as `θ · I` with real angle `θ = 2π · j.val / 5`. -/
theorem omegaPow_eq_exp_mul_I (j : Fin 5) :
    omegaPow j = exp (((2 * Real.pi * (j.val : ℝ) / 5 : ℝ) : ℂ) * I) := by
  rw [omegaPow_eq_exp]
  congr 1
  push_cast
  ring

/-- **Cosine identity for the 5-th roots.**
`ωʲ + ω⁻ʲ = 2 cos(2π · j.val / 5)` (as complex numbers). -/
theorem omegaPow_add_inv_eq_two_cos (j : Fin 5) :
    omegaPow j + omegaPow (-j) =
      (2 : ℂ) * Real.cos (2 * Real.pi * (j.val : ℝ) / 5) := by
  set θ : ℝ := 2 * Real.pi * (j.val : ℝ) / 5
  have hpos : omegaPow j = exp ((θ : ℂ) * I) := by
    simpa [θ] using omegaPow_eq_exp_mul_I j
  have hneg : omegaPow (-j) = exp (-(θ : ℂ) * I) := by
    -- `ω^{-j} = (ω^j)⁻¹ = exp(−θ I)`
    rw [omegaPow_neg, hpos, ← exp_neg]
    congr 1
    ring
  -- `2 · Complex.cos θ = exp(θ I) + exp(−θ I)`, and `↑(Real.cos θ) = Complex.cos θ`
  calc
    omegaPow j + omegaPow (-j)
        = exp ((θ : ℂ) * I) + exp (-(θ : ℂ) * I) := by rw [hpos, hneg]
    _   = 2 * Complex.cos (θ : ℂ) := (Complex.two_cos (θ : ℂ)).symm
    _   = 2 * (Real.cos θ : ℂ) := by rw [← Complex.ofReal_cos]
    _   = (2 : ℂ) * Real.cos (2 * Real.pi * (j.val : ℝ) / 5) := by rfl

/-- **Mode eigenrelation (cosine form).**
`A vⱼ = (2 cos(2π · j.val / 5)) • vⱼ`. -/
theorem adjacency_eigenmode_cos (j : Fin 5) :
    adjacency (eigenmode j) =
      ((2 : ℂ) * Real.cos (2 * Real.pi * (j.val : ℝ) / 5)) • eigenmode j := by
  rw [adjacency_eigenmode, omegaPow_add_inv_eq_two_cos]

/-! ### Graph Laplacian `L = 2I − A` -/

/-- Laplacian of the 2-regular 5-cycle: `L f = 2 · f − A f`. -/
noncomputable def laplacian (f : VertexSpace) : VertexSpace :=
  (2 : ℂ) • f - adjacency f

theorem laplacian_apply (f : VertexSpace) (x : Fin 5) :
    laplacian f x = (2 : ℂ) * f x - adjacency f x := by
  simp [laplacian, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem laplacian_eq (f : VertexSpace) :
    laplacian f = (2 : ℂ) • f - adjacency f :=
  rfl

theorem laplacian_add (f g : VertexSpace) :
    laplacian (f + g) = laplacian f + laplacian g := by
  ext x
  simp only [laplacian_apply, adjacency_apply, Pi.add_apply]
  ring

theorem laplacian_smul (c : ℂ) (f : VertexSpace) :
    laplacian (c • f) = c • laplacian f := by
  ext x
  simp only [laplacian_apply, adjacency_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Linear map form of the cycle Laplacian. -/
noncomputable def laplacianLinear : VertexSpace →ₗ[ℂ] VertexSpace where
  toFun := laplacian
  map_add' := laplacian_add
  map_smul' := by
    intro c f
    simpa using laplacian_smul c f

@[simp] theorem laplacianLinear_apply (f : VertexSpace) :
    laplacianLinear f = laplacian f :=
  rfl

/-- **Laplacian eigenrelation.**
`L vⱼ = (2 − 2 cos(2π · j.val / 5)) • vⱼ`. -/
theorem laplacian_eigenmode (j : Fin 5) :
    laplacian (eigenmode j) =
      ((2 : ℂ) - 2 * Real.cos (2 * Real.pi * (j.val : ℝ) / 5)) • eigenmode j := by
  -- `2 • v − (2 cos θ) • v = (2 − 2 cos θ) • v` by `sub_smul`
  rw [laplacian, adjacency_eigenmode_cos, ← sub_smul]

/-- Special case `j = 0`: constant mode is a kernel vector of `L`. -/
theorem laplacian_eigenmode_zero :
    laplacian (eigenmode 0) = 0 := by
  rw [laplacian_eigenmode]
  simp [Real.cos_zero]

/-- Special case `j = 0` for adjacency: constant mode has eigenvalue `2`. -/
theorem adjacency_eigenmode_zero :
    adjacency (eigenmode 0) = (2 : ℂ) • eigenmode 0 := by
  rw [adjacency_eigenmode_cos]
  simp [Real.cos_zero]

/-! ### Isotypic projectors preserve eigenspaces of `A` / `L` -/

/-- On Fourier modes, the isotypic projector is a scalar multiple of the
identity, so it automatically preserves the `A`-eigenspace structure:
`A (Pⱼ vₗ) = λₗ · (Pⱼ vₗ)`. -/
theorem adjacency_isotypicProjector_eigenmode (j ℓ : Fin 5) :
    adjacency (isotypicProjector j (eigenmode ℓ)) =
      ((2 : ℂ) * Real.cos (2 * Real.pi * (ℓ.val : ℝ) / 5)) •
        isotypicProjector j (eigenmode ℓ) := by
  rw [isotypicProjector_eigenmode, adjacency_smul, adjacency_eigenmode_cos, smul_comm]

/-- Same for the Laplacian. -/
theorem laplacian_isotypicProjector_eigenmode (j ℓ : Fin 5) :
    laplacian (isotypicProjector j (eigenmode ℓ)) =
      ((2 : ℂ) - 2 * Real.cos (2 * Real.pi * (ℓ.val : ℝ) / 5)) •
        isotypicProjector j (eigenmode ℓ) := by
  rw [isotypicProjector_eigenmode, laplacian_smul, laplacian_eigenmode, smul_comm]

/-- Projectors and adjacency commute on the Fourier basis:
`A ∘ Pⱼ = Pⱼ ∘ A` when evaluated on eigenmodes. -/
theorem adjacency_commute_isotypicProjector_eigenmode (j ℓ : Fin 5) :
    adjacency (isotypicProjector j (eigenmode ℓ)) =
      isotypicProjector j (adjacency (eigenmode ℓ)) := by
  rw [adjacency_isotypicProjector_eigenmode, adjacency_eigenmode_cos,
    isotypicProjector_smul]

/-- Projectors and Laplacian commute on the Fourier basis. -/
theorem laplacian_commute_isotypicProjector_eigenmode (j ℓ : Fin 5) :
    laplacian (isotypicProjector j (eigenmode ℓ)) =
      isotypicProjector j (laplacian (eigenmode ℓ)) := by
  rw [laplacian_isotypicProjector_eigenmode, laplacian_eigenmode,
    isotypicProjector_smul]

end Brockian.D5LaplacianModes
