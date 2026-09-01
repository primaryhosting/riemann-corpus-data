import Mathlib
namespace Brockian.MsLYM
/-- The Lubell–Yamamoto–Meshalkin inequality: for an antichain 𝒜 in the Boolean lattice on a
    finite type, ∑_{A ∈ 𝒜} 1/C(|α|, |A|) ≤ 1. -/
theorem lym {α : Type*} [Fintype α] [DecidableEq α] (𝒜 : Finset (Finset α))
    (h : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    ∑ A ∈ 𝒜, (1 : ℚ) / ((Fintype.card α).choose A.card) ≤ 1 := by
  simpa [one_div] using
    Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) h
end Brockian.MsLYM

