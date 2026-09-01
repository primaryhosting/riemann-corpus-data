import Mathlib
namespace C2.SetT

/-- Zorn's lemma: if every chain in a partial order has an upper bound, there is a
maximal element. Follows from `exists_maximal_of_chains_bounded` plus antisymmetry. -/
theorem zorn (α : Type*) [PartialOrder α] (h : ∀ c : Set α, IsChain (· ≤ ·) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
    ∃ m : α, ∀ a, m ≤ a → a = m := by
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded h (fun {_ _ _} hab hbc => le_trans hab hbc)
  exact ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩

/-- Schröder–Bernstein: mutual injections give a bijection. -/
theorem schroeder_bernstein2 {α β : Type*} (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (α ≃ β) :=
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

/-- Cantor's theorem: no map `α → Set α` is surjective. -/
theorem cantor_powerset {α : Type*} : ¬ ∃ f : α → Set α, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact Function.cantor_surjective f hf

end C2.SetT

