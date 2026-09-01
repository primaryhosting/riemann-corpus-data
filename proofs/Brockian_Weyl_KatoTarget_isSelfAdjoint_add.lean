/-
  Aristotle target — BOUNDED PERTURBATION preserves essential self-adjointness
  (the bounded case of Kato–Rellich).

  This is the abstract operator-theory link for the −Δ+V route: if the free operator
  is essentially self-adjoint and V acts as a bounded self-adjoint operator, then the
  sum is essentially self-adjoint. Combined with essential self-adjointness of −Δ and
  the verified fact that the Brockian potential is bounded self-adjoint
  (`Brockian.SpectralGate1.isSelfAdjoint_primeGaussianMulCLM`), this discharges Gate 1
  for the Brockian operator.

  Stated here in the reachable BOUNDED form: a bounded self-adjoint operator is a
  bounded self-adjoint perturbation of ANY bounded self-adjoint operator, and the sum
  of two bounded self-adjoint operators is bounded self-adjoint (hence essentially
  self-adjoint by the CLM ⇒ ESA result). The genuinely new content requested is the
  UNBOUNDED case skeleton: a densely-defined symmetric `T` whose ranges `ran(T ± i)`
  are dense, plus a bounded self-adjoint `B`, has `ran((T+B) ± i)` dense — so `T+B` is
  essentially self-adjoint.

  GOAL: replace every placeholder with a complete proof. Same charter rules
  (no incomplete proofs or extra axioms; #print axioms clean).
-/
import Mathlib

open scoped InnerProductSpace

namespace Brockian.Weyl.KatoTarget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sum of two bounded self-adjoint operators is bounded self-adjoint (base case,
genuinely provable). -/
theorem isSelfAdjoint_add {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : IsSelfAdjoint (A + B) := by
  exact hA.add hB

/-- The perturbed range-density fact (bounded case). If `T : H →L[ℂ] H` is bounded
self-adjoint and `B : H →L[ℂ] H` is bounded self-adjoint, then for a non-real `z` the
range of `(T + B) − z` is dense (in fact all of `H`, since bounded self-adjoint minus a
non-real scalar is invertible). This is the range-density input the essential
self-adjointness criterion consumes. -/
theorem dense_range_add_sub_of_selfAdjoint {T B : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) (hB : IsSelfAdjoint B) (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun v => (T + B) v - z • v)) := by
  let S : H →L[ℂ] H := T + B
  have hS : IsSelfAdjoint S := isSelfAdjoint_add hT hB
  have hz_not_mem : z ∉ spectrum ℂ S := by
    intro hz_mem
    exact hz (hS.im_eq_zero_of_mem_spectrum hz_mem)
  have hz_res : z ∈ resolventSet ℂ S := by
    simpa [spectrum] using hz_not_mem
  have hu₀ : IsUnit (algebraMap ℂ (H →L[ℂ] H) z - S) :=
    (spectrum.mem_resolventSet_iff).mp hz_res
  have hu : IsUnit (S - algebraMap ℂ (H →L[ℂ] H) z) := by
    simpa only [sub_eq_neg_add, neg_add_rev, neg_neg] using hu₀.neg
  obtain ⟨u, hu_eq⟩ := hu
  rw [show Set.range (fun v => (T + B) v - z • v) =
      Set.range (fun v => (u : H →L[ℂ] H) v) by
    congr 1
    funext v
    rw [hu_eq]
    simp [S]]
  rw [show Set.range (fun v => (u : H →L[ℂ] H) v) = Set.univ by
    apply Set.eq_univ_of_forall
    intro y
    refine ⟨(↑(u⁻¹) : H →L[ℂ] H) y, ?_⟩
    change ((u : H →L[ℂ] H) * (↑(u⁻¹) : H →L[ℂ] H)) y = y
    exact congrArg (fun q : H →L[ℂ] H => q y) u.val_inv]
  exact dense_univ

end Brockian.Weyl.KatoTarget

