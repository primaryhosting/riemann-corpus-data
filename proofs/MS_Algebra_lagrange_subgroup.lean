import Mathlib
namespace MS.Algebra

theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  classical
  simpa using Subgroup.card_subgroup_dvd_card H

/-- Cayley–Hamilton. The original statement used `Polynomial.C` as the coefficient map,
which does not typecheck (`eval₂` needs a ring hom `ℂ →+* Matrix (Fin n) (Fin n) ℂ`);
it has been replaced by the canonical `algebraMap`, which is the intended meaning. -/
theorem cayley_hamilton {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.eval₂ (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)) M = 0 :=
  M.aeval_self_charpoly

theorem cauchy_theorem_group {G : Type*} [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  exists_prime_orderOf_dvd_card p hd

theorem freshmans_dream (p : ℕ) [Fact p.Prime] (a b : ZMod p) : (a + b) ^ p = a ^ p + b ^ p :=
  add_pow_char a b p

theorem cayley_embedding {G : Type*} [Group G] :
    ∃ f : G →* Equiv.Perm G, Function.Injective f :=
  ⟨MulAction.toPermHom G G, fun a b h => by
    simpa using congrArg (fun e : Equiv.Perm G => e 1) h⟩

end MS.Algebra

