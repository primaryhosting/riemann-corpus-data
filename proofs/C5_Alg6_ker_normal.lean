import Mathlib
namespace C5.Alg6

/-- The kernel of a group homomorphism is a normal subgroup. -/
theorem ker_normal {G H : Type*} [Group G] [Group H] (f : G →* H) : (f.ker).Normal :=
  inferInstance

/-- Lagrange's theorem: the index of a subgroup times its cardinality is the
cardinality of the group. -/
theorem index_mul_card {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    H.index * Fintype.card H = Fintype.card G := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Subgroup.index_mul_card]

/-- Conjugation preserves the order of an element. -/
theorem conj_preserves_order {G : Type*} [Group G] (g a : G) :
    orderOf (g * a * g⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  simpa [MulAut.conj] using this

end C5.Alg6

