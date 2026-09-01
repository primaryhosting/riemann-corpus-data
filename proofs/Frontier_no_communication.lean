import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Kronecker BigOperators Matrix

namespace Frontier

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private theorem sum_swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d
      = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- Partial trace over the second (Bob's) factor of a bipartite operator. -/
noncomputable def ptraceB (ρ : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  Matrix.of fun i j => ∑ b : B, ρ (i, b) (j, b)

/-- **No-communication theorem.**  Any local quantum operation performed on Bob's half of a
bipartite state (a completely positive trace-preserving map given in Kraus form
`ρ ↦ ∑ k (1 ⊗ Kₖ) ρ (1 ⊗ Kₖ)†` with `∑ k Kₖ† Kₖ = 1`) leaves Alice's reduced density matrix
completely unchanged; hence no information can be transmitted to Alice by Bob's actions. -/
theorem no_communication {K : Type*} [Fintype K]
    (ρ : Matrix (A × B) (A × B) ℂ) (Kr : K → Matrix B B ℂ)
    (hK : ∑ k, (Kr k)ᴴ * (Kr k) = 1) :
    ptraceB (∑ k, (1 ⊗ₖ Kr k) * ρ * (1 ⊗ₖ Kr k)ᴴ) = ptraceB ρ := by
  ext i j
  have hK' : ∀ s q : B, ∑ k, ∑ b : B, (starRingEnd ℂ) (Kr k b s) * Kr k b q =
      if s = q then (1 : ℂ) else 0 := by
    intro s q
    have := congrArg (fun M : Matrix B B ℂ => M s q) hK
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
      using this
  simp only [ptraceB, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type_right, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, star_mul', apply_ite (star : ℂ → ℂ), star_one, star_zero, mul_ite,
    mul_zero]
  have step : ∀ q s : B, ∑ b : B, ∑ k, Kr k b q * ρ (i, q) (j, s) * star (Kr k b s)
      = ρ (i, q) (j, s) * (if s = q then 1 else 0) := by
    intro q s
    rw [← hK' s q, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [starRingEnd_apply]
    ring
  calc ∑ b : B, ∑ k, ∑ s : B, (∑ q : B, Kr k b q * ρ (i, q) (j, s)) * star (Kr k b s)
      = ∑ b : B, ∑ k, ∑ s : B, ∑ q : B, Kr k b q * ρ (i, q) (j, s) * star (Kr k b s) := by
        simp [Finset.sum_mul]
    _ = ∑ s : B, ∑ q : B, ∑ b : B, ∑ k, Kr k b q * ρ (i, q) (j, s) * star (Kr k b s) :=
        sum_swap4 _
    _ = ∑ s : B, ∑ q : B, ρ (i, q) (j, s) * (if s = q then 1 else 0) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun q _ => step q s
    _ = ∑ b : B, ρ (i, b) (j, b) := by simp

end Frontier

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

