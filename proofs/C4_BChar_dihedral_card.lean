import Mathlib
namespace C4.BChar

/-- The dihedral group of order `2n` has exactly `2n` elements. -/
theorem dihedral_card (n : ℕ) [NeZero n] : Nat.card (DihedralGroup n) = 2*n :=
  DihedralGroup.nat_card

/-- The unit group of `ZMod 5` has 4 elements. -/
theorem zmod5_units_card : Fintype.card (ZMod 5)ˣ = 4 := by decide

/-- `(ZMod 5)ˣ` is cyclic of order 4: `2` is a generator. -/
theorem cyclic_gen_zmod5 : ∃ g : (ZMod 5)ˣ, orderOf g = 4 := by
  refine ⟨ZMod.unitOfCoprime 2 (by decide), ?_⟩
  have h := orderOf_eq_prime_pow
    (x := ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5)) (p := 2) (n := 1)
    (by decide) (by decide)
  simpa using h

end C4.BChar

