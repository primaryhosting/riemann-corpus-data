import Mathlib
namespace C2.CS2

/-- No boolean equals its own negation. -/
theorem no_universal_decider : ¬ ∃ b : Bool, b = !b := by
  rintro ⟨b, hb⟩
  cases b <;> simp at hb

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/
theorem diagonal_argument {α : Type*} (f : α → (α → Bool)) : ¬ Function.Surjective f := by
  intro hs
  obtain ⟨a, ha⟩ := hs (fun x => !(f x x))
  have h := congrFun ha a
  simp at h

/-- Pigeonhole principle for functions between finite types. -/
theorem pigeon_functions {A B : Type*} [Fintype A] [Fintype B] (h : Fintype.card B < Fintype.card A)
    (f : A → B) : ∃ x y, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h

end C2.CS2

