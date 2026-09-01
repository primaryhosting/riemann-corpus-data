import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
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

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/
def ksVec : Fin 18 → (Fin 4 → ℝ) :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 0], ![1, -1, 0, 0],
    ![0, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, -1, 0],
    ![1, -1, 1, -1], ![1, -1, -1, 1], ![0, 0, 1, 1],
    ![1, 1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0],
    ![1, 1, -1, 1], ![1, 1, 1, -1], ![-1, 1, 1, 1]]

/-- The 9 orthogonal bases of the Kochen–Specker set, given as quadruples of indices into
`ksVec`.  Each of the 18 vectors occurs in exactly two of these bases. -/
def ksBasis : Fin 9 → (Fin 4 → Fin 18) :=
  ![![0, 1, 2, 3], ![0, 4, 5, 6], ![7, 8, 2, 9], ![7, 10, 6, 11], ![1, 4, 12, 13],
    ![8, 10, 13, 14], ![15, 16, 3, 9], ![15, 17, 5, 11], ![16, 17, 12, 14]]

/-- Each of the 18 vectors is nonzero. -/
theorem ksVec_ne_zero (j : Fin 18) : ksVec j ≠ 0 := by
  fin_cases j <;> simp [ksVec, funext_iff, Fin.forall_fin_succ]

/-- The 18 vectors are pairwise distinct. -/
theorem ksVec_injective : Function.Injective ksVec := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp_all [ksVec, funext_iff, Fin.forall_fin_succ] <;> norm_num at hab

/-- Each of the 9 quadruples consists of pairwise orthogonal vectors, hence is an orthogonal
basis of `ℝ⁴`. -/
theorem ksBasis_orthogonal (b : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    ∑ k : Fin 4, ksVec (ksBasis b i) k * ksVec (ksBasis b j) k = 0 := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp_all [ksVec, ksBasis, Fin.sum_univ_succ]

/-- Each of the 18 vectors occurs in exactly two of the 9 bases: summing any weight function
over all the (basis, position) pairs counts every vector exactly twice. -/
theorem ksBasis_double_count (g : Fin 18 → ℕ) :
    ∑ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 2 * ∑ j : Fin 18, g j := by
  simp [ksBasis, Fin.sum_univ_succ]
  ring

/-- **Kochen–Specker (18 vectors).**  There is no `{0,1}`-coloring of the 18 vectors of
`ksVec` such that in each of the 9 orthogonal bases exactly one vector is colored `1`. -/
theorem kochen_specker_18 :
    ¬ ∃ f : (Fin 4 → ℝ) → Bool,
      ∀ b : Fin 9,
        ((Finset.univ : Finset (Fin 4)).filter fun i => f (ksVec (ksBasis b i)) = true).card = 1 := by
  rintro ⟨f, hf⟩
  set g : Fin 18 → ℕ := fun j => if f (ksVec j) = true then 1 else 0 with hg
  have hrow : ∀ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 1 := by
    intro b
    have := hf b
    rw [Finset.card_filter] at this
    simpa [hg] using this
  have h9 : ∑ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 9 := by
    simp [hrow]
  rw [ksBasis_double_count g] at h9
  omega

end Phys

