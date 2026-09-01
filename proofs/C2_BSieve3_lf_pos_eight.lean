import Mathlib
namespace C2.BSieve3
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ)/p) / ((1 - 1/(p:ℝ))^G.card) else 1

/-- The local factor of the admissible 8-tuple `{0,2,6,8,12,18,20,26}` is positive at
every `p`.  For non-primes the factor is `1`; for primes one checks `ν(p) < p`
directly for `p ≤ 8` and uses `ν(p) ≤ |G| = 8 < p` otherwise. -/
theorem lf_pos_eight (p : ℕ) : 0 < localFactor ({0,2,6,8,12,18,20,26} : Finset ℕ) p := by
  by_cases hp : p.Prime
  · have h2 : 2 ≤ p := hp.two_le
    have hp0 : (0:ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le two_pos h2
    have hnu : nu ({0,2,6,8,12,18,20,26} : Finset ℕ) p < p := by
      rcases le_or_gt p 8 with h | h
      · interval_cases p <;> first | (exfalso; revert hp; decide) | decide
      · exact lt_of_le_of_lt (le_trans Finset.card_image_le (by decide)) h
    rw [localFactor, if_pos hp]
    apply div_pos
    · rw [sub_pos, div_lt_one hp0]
      exact_mod_cast hnu
    · apply pow_pos
      rw [sub_pos, div_lt_one hp0]
      exact_mod_cast h2
  · rw [localFactor, if_neg hp]; norm_num

/-- The number of residues occupied by `G` mod `p` is at most both `|G|` and `p`. -/
theorem nu_le_min (G : Finset ℕ) (p : ℕ) (hp : 0 < p) : nu G p ≤ min G.card p := by
  refine le_min Finset.card_image_le ?_
  have hsub : G.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  simpa using Finset.card_le_card hsub

/-- For nonzero `g` in `ZMod 13`, exactly `11` residues avoid both `0` and `-g`. -/
theorem admissible_count_thirteen (g : ZMod 13) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 13 => r ≠ 0 ∧ r ≠ -g)).card = 11 := by
  revert g; decide

end C2.BSieve3

