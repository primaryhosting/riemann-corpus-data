import Mathlib
namespace MS2.CSLogic

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/
theorem cantor_diagonal {α : Type*} (f : α → (α → Bool)) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x => !(f x x))
  have : f a a = !(f a a) := congrFun ha a
  simp at this

/-- There is no injection from the powerset of `α` into `α`. -/
theorem no_injection_powerset {α : Type*} (f : Set α → α) : ¬ Function.Injective f :=
  Function.cantor_injective f

theorem fixed_point_free_negation : ¬ ∃ b : Bool, b = !b := by
  rintro ⟨b, hb⟩
  cases b <;> simp at hb

theorem countable_union_countable {α : Type*} (s : ℕ → Set α) (h : ∀ n, (s n).Countable) :
    (⋃ n, s n).Countable :=
  Set.countable_iUnion h

theorem finite_no_surj_to_larger {A B : Type*} [Fintype A] [Fintype B]
    (h : Fintype.card A < Fintype.card B) (f : A → B) : ¬ Function.Surjective f := by
  intro hf
  exact absurd (Fintype.card_le_of_surjective f hf) (not_le.mpr h)

end MS2.CSLogic

