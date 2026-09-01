import Mathlib
namespace Frontier.AlgebraLogic
theorem lagrange {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H
theorem cantor {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f
theorem cayley_embedding {G : Type*} [Group G] : ∃ f : G →* Equiv.Perm G, Function.Injective f :=
  ⟨MulAction.toPermHom G G, by
    intro a b hab
    have := congrArg (fun p : Equiv.Perm G => p 1) hab
    simpa [MulAction.toPermHom] using this⟩
end Frontier.AlgebraLogic

