import Mathlib

/-!
# Qf Add
Category: Linalg
Target: Zeta23Redux.LinAlg.qf_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux
namespace LinAlg

/-- The quadratic form associated to a complex matrix `M`, evaluated at a vector `x`
of Euclidean space: `qf M x = ∑ i, ∑ j, conj (x i) * M i j * x j`, i.e. `xᴴ M x`. -/
noncomputable def qf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (x i) * M i j * x j

/-- `qf M x` is indeed the sesquilinear expression `xᴴ M x`. -/
theorem qf_eq_dotProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    qf M x = star x.ofLp ⬝ᵥ M.mulVec x.ofLp := by
  simp only [qf, dotProduct, Matrix.mulVec, Pi.star_apply, starRingEnd_apply,
    Finset.mul_sum, mul_assoc]

/-- Quadratic-form additivity: `qf (M + N) x = qf M x + qf N x`. -/
theorem qf_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    qf (M + N) x = qf M x + qf N x := by
  simp only [qf, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

end LinAlg
end Zeta23Redux

