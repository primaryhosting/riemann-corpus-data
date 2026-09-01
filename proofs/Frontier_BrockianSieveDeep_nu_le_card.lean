import Mathlib
namespace Frontier.BrockianSieveDeep
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

theorem nu_le_card (G : Finset ℕ) (p : ℕ) : nu G p ≤ G.card :=
  Finset.card_image_le

theorem nu_le_prime (G : Finset ℕ) (p : ℕ) (hp : 0 < p) : nu G p ≤ p := by
  have hsub : G.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  simpa [nu] using (Finset.card_le_card hsub).trans_eq (Finset.card_range p)

theorem nu_singleton_lt (a p : ℕ) (hp : 2 ≤ p) : nu {a} p < p := by
  have : nu {a} p ≤ 1 := by simpa using nu_le_card {a} p
  omega

end Frontier.BrockianSieveDeep

