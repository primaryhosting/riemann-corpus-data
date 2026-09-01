import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexConjugate

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QPhys

/-- **Ground-state variational bound.**

Let `H` be a Hamiltonian (a linear operator on a complex inner product space `E`) which is
diagonalized by an orthonormal basis `b` of eigenvectors, with real eigenvalues `Ev i`, and
suppose `E₀` is a lower bound for the spectrum (`E₀ ≤ Ev i` for every `i`, so `E₀` may be taken
to be the ground-state energy). Then for every nonzero state `ψ`, the Rayleigh quotient
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`.

Here `⟨ψ|ψ⟩ = ‖ψ‖ ^ 2` and `⟨ψ|H|ψ⟩ = inner ℂ ψ (H ψ)`, whose real part is taken since the
Rayleigh quotient is compared with a real number (under these hypotheses the inner product is
in fact real). -/
theorem variational_bound {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (H : E →ₗ[ℂ] E) (Ev : ι → ℝ) (E₀ : ℝ)
    (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i) (hE : ∀ i, E₀ ≤ Ev i)
    (ψ : E) (hψ : ψ ≠ 0) :
    E₀ ≤ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 := by
  set c : ι → ℂ := fun i => (b.repr ψ).ofLp i with hc
  -- Parseval: the squared norm of `ψ` is the sum of the squared moduli of its coordinates.
  have hnorm : ‖ψ‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have hiso := b.repr.norm_map ψ
    rw [← hiso, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  -- `H` acts diagonally on the coordinates of `ψ`.
  have hHψ : H ψ = ∑ i, ((Ev i : ℂ) * c i) • b i := by
    conv_lhs => rw [← b.sum_repr ψ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hH i, smul_smul, mul_comm]
  -- Hence the expectation value is the weighted average `∑ Ev i * |c i| ^ 2`.
  have hinner : (inner ℂ ψ (H ψ)) = ((∑ i, Ev i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hHψ, inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    have hbi : (inner ℂ ψ (b i) : ℂ) = conj (c i) := by
      rw [hc]; simp [b.repr_apply_apply, inner_conj_symm]
    rw [hbi, mul_assoc, Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [hinner, Complex.ofReal_re, le_div_iff₀ hpos, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    have hi := hE i
    nlinarith [sq_nonneg ‖c i‖]

end QPhys

