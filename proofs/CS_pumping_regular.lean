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

namespace CS

/-- **Pumping lemma for regular languages.**
Every regular language `L` admits a pumping length `p > 0` such that every word `x ∈ L`
of length at least `p` can be split as `x = a ++ b ++ c` with `|a| + |b| ≤ p`, `b ≠ []`,
and `a ++ bⁿ ++ c ∈ L` for every `n : ℕ`. -/
theorem pumping_regular {α : Type*} (L : Language α) (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ x ∈ L, p ≤ x.length →
      ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ p ∧ b ≠ [] ∧
        ∀ n : ℕ, a ++ (List.replicate n b).flatten ++ c ∈ L := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  refine ⟨Fintype.card σ + 1, Nat.succ_pos _, ?_⟩
  intro x hx hlen
  obtain ⟨a, b, c, hxabc, hab, hbnil, hsub⟩ := M.pumping_lemma hx (by omega)
  refine ⟨a, b, c, hxabc, by omega, hbnil, ?_⟩
  intro n
  apply hsub
  refine ⟨a ++ (List.replicate n b).flatten, ⟨a, rfl, (List.replicate n b).flatten, ?_, rfl⟩,
    c, rfl, by simp⟩
  rw [Language.mem_kstar]
  exact ⟨List.replicate n b, rfl, fun y hy => by
    simpa using (List.eq_of_mem_replicate hy)⟩

end CS

