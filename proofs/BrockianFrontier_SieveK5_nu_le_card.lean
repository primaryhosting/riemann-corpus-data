import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

/-- Hardy–Littlewood local factor of a gap-set at a prime. -/
noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ) / p) / ((1 - 1 / (p : ℝ)) ^ G.card) else 1

/-- The number of covered residues never exceeds the size of the gap-set. -/
lemma nu_le_card (G : Finset ℕ) (p : ℕ) : nu G p ≤ G.card :=
  Finset.card_image_le

/-- General positivity criterion: if `G` misses a residue class modulo every prime
    `q ≤ G.card`, then all its local factors are positive.  (For `q > G.card` the
    gap-set cannot cover all residues, since `nu G q ≤ G.card < q`.) -/
lemma localFactor_pos_of_small_primes (G : Finset ℕ)
    (h : ∀ q : ℕ, q.Prime → q ≤ G.card → nu G q < q) (p : ℕ) :
    0 < localFactor G p := by
  unfold localFactor
  split_ifs with hp
  · have hp2 : 2 ≤ p := hp.two_le
    have hp0 : (0 : ℝ) < p := by positivity
    have hnu : nu G p < p := by
      by_cases hle : p ≤ G.card
      · exact h p hp hle
      · exact lt_of_le_of_lt (nu_le_card G p) (by omega)
    have hnum : 0 < 1 - (nu G p : ℝ) / p := by
      have : (nu G p : ℝ) / p < 1 := by
        rw [div_lt_one hp0]; exact_mod_cast hnu
      linarith
    have hden : 0 < (1 - 1 / (p : ℝ)) ^ G.card := by
      apply pow_pos
      have : (1 : ℝ) / p ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left <;> [norm_num; norm_num; exact_mod_cast hp2]
      linarith
    exact div_pos hnum hden
  · norm_num

/-- Positivity of every local factor for the admissible 5-tuple `{0,2,6,8,12}`
    (extends the verified twin/triple/quadruple positivity to k = 5). -/
theorem localFactor_pos_five (p : ℕ) :
    0 < localFactor ({0, 2, 6, 8, 12} : Finset ℕ) p := by
  apply localFactor_pos_of_small_primes
  intro q hq hle
  have hle5 : q ≤ 5 := by
    have hc : ({0, 2, 6, 8, 12} : Finset ℕ).card = 5 := by decide
    omega
  interval_cases q <;> revert hq <;> simp [nu] <;> decide

/-- Positivity for a second admissible 5-tuple `{0,4,6,10,12}`. -/
theorem localFactor_pos_five' (p : ℕ) :
    0 < localFactor ({0, 4, 6, 10, 12} : Finset ℕ) p := by
  apply localFactor_pos_of_small_primes
  intro q hq hle
  have hle5 : q ≤ 5 := by
    have hc : ({0, 4, 6, 10, 12} : Finset ℕ).card = 5 := by decide
    omega
  interval_cases q <;> revert hq <;> simp [nu] <;> decide

/-- Positivity for the admissible 6-tuple `{0,4,6,10,12,16}`. -/
theorem localFactor_pos_six (p : ℕ) :
    0 < localFactor ({0, 4, 6, 10, 12, 16} : Finset ℕ) p := by
  apply localFactor_pos_of_small_primes
  intro q hq hle
  have hle6 : q ≤ 6 := by
    have hc : ({0, 4, 6, 10, 12, 16} : Finset ℕ).card = 6 := by decide
    omega
  interval_cases q <;> revert hq <;> simp [nu] <;> decide

end BrockianFrontier.SieveK5

