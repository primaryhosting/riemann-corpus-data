import Mathlib
/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the requested header comment is placed immediately after `import Mathlib`.

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

namespace QPhys

open RCLike ComplexConjugate

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E}

/-- Parseval: the squared norm of `ψ` is the sum of the squared moduli of its
coordinates in an eigenvector basis of `H`. -/
theorem norm_sq_eq_sum_eigencoords (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n) (ψ : E) :
    ‖ψ‖ ^ 2 = ∑ i, ‖(hH.eigenvectorBasis hn).repr ψ i‖ ^ 2 := by
  rw [← (hH.eigenvectorBasis hn).repr.norm_map ψ, EuclideanSpace.norm_eq,
    Real.sq_sqrt (by positivity)]

/-- The expectation value `⟨ψ|H|ψ⟩` expanded in an eigenvector basis of `H`:
it is the eigenvalue-weighted sum of the squared moduli of the coordinates of `ψ`. -/
theorem re_inner_apply_eq_sum_eigenvalues (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (ψ : E) :
    RCLike.re (inner ℂ ψ (H ψ)) =
      ∑ i, hH.eigenvalues hn i * ‖(hH.eigenvectorBasis hn).repr ψ i‖ ^ 2 := by
  have h1 : inner ℂ ψ (H ψ) = inner ℂ ((hH.eigenvectorBasis hn).repr ψ)
      ((hH.eigenvectorBasis hn).repr (H ψ)) :=
    ((hH.eigenvectorBasis hn).repr.inner_map_map ψ (H ψ)).symm
  rw [h1, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have key : ∀ (a : ℝ) (z : ℂ), RCLike.re ((a : ℂ) * z * conj z) = a * ‖z‖ ^ 2 := by
    intro a z
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [hH.eigenvectorBasis_apply_self_apply hn ψ i, RCLike.inner_apply]
  exact key _ _

/-- **Variational principle (Rayleigh–Ritz bound).**
Let `H` be a self-adjoint (symmetric) operator on a finite-dimensional complex inner product
space, and let `E₀` be a lower bound for its eigenvalues (the ground-state energy).  Then for
every nonzero state `ψ`, the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`. -/
theorem variational_bound (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ hH.eigenvalues hn i) {ψ : E} (hψ : ψ ≠ 0) :
    E₀ ≤ RCLike.re (inner ℂ ψ (H ψ)) / RCLike.re (inner ℂ ψ ψ) := by
  have hnorm : RCLike.re (inner ℂ ψ ψ) = ‖ψ‖ ^ 2 := inner_self_eq_norm_sq ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [hnorm, le_div_iff₀ hpos, re_inner_apply_eq_sum_eigenvalues hH hn ψ,
    norm_sq_eq_sum_eigencoords hH hn ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

omit [FiniteDimensional ℂ E] in
/-- The bound of `QPhys.variational_bound` is sharp: it is attained at a ground state,
i.e. at an eigenvector of `H` with eigenvalue `E₀`. -/
theorem variational_bound_eq_of_eigenvector {E₀ : ℝ} {ψ : E} (hψ : ψ ≠ 0)
    (hHψ : H ψ = (E₀ : ℂ) • ψ) :
    RCLike.re (inner ℂ ψ (H ψ)) / RCLike.re (inner ℂ ψ ψ) = E₀ := by
  have hnorm : RCLike.re (inner ℂ ψ ψ) = ‖ψ‖ ^ 2 := inner_self_eq_norm_sq ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  have hnum : RCLike.re (inner ℂ ψ (H ψ)) = E₀ * ‖ψ‖ ^ 2 := by
    rw [hHψ, inner_smul_right]
    simp [← Complex.ofReal_pow]
  rw [hnum, hnorm, mul_div_assoc, div_self hpos.ne', mul_one]

end QPhys

