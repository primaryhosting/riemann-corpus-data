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

namespace Brockian.QuantumFiniteSpectral

/-- Quantitative pigeonhole: if every fibre of `f : α → β` has at most `k` elements,
then `|α| ≤ k * |β|`. -/
theorem card_le_of_pairwise_distinct_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (k : ℕ)
    (h : ∀ b : β, (Finset.univ.filter fun a => f a = b).card ≤ k) :
    Fintype.card α ≤ k * Fintype.card β := by
  classical
  have key : (Finset.univ : Finset α).card
      = ∑ b ∈ (Finset.univ : Finset β), (Finset.univ.filter fun a => f a = b).card :=
    Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (f a))
  have hle : (Finset.univ : Finset α).card ≤ ∑ _b ∈ (Finset.univ : Finset β), k := by
    rw [key]; exact Finset.sum_le_sum (fun b _ => h b)
  rw [Finset.sum_const, smul_eq_mul] at hle
  simpa [Finset.card_univ, mul_comm] using hle

end Brockian.QuantumFiniteSpectral

