import Mathlib
namespace BrockianFrontier.SingularSeries

/-- Number of residues covered by `G` modulo `p`. -/
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

/-- The Hardy–Littlewood local factor of an admissible set `G` at `p`. -/
noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ) / p) / ((1 - 1 / (p : ℝ)) ^ G.card) else 1

/-- Admissibility (`nu G p < p` at every prime `p`) forces the local factor to be positive. -/
theorem localFactor_pos_of_lt (G : Finset ℕ) (p : ℕ) (h : p.Prime → nu G p < p) :
    0 < localFactor G p := by
  unfold localFactor
  split_ifs with hp
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply div_pos
    · rw [sub_pos, div_lt_one hp0]
      exact_mod_cast h hp
    · exact pow_pos (by rw [sub_pos, div_lt_one hp0]; exact_mod_cast hp.one_lt) _
  · norm_num

/-- Every local factor of the admissible prime triple `{0,2,6}` is strictly positive.
    (Extends the verified twin-gap `{0,2}` positivity to k = 3.) -/
theorem localFactor_pos_triple (p : ℕ) : 0 < localFactor ({0, 2, 6} : Finset ℕ) p := by
  refine localFactor_pos_of_lt _ _ (fun hp => ?_)
  have hp2 := hp.two_le
  have hle : nu ({0, 2, 6} : Finset ℕ) p ≤ 3 :=
    le_trans Finset.card_image_le (by decide)
  rcases Nat.lt_or_ge p 4 with hlt | hge
  · interval_cases p <;> decide
  · omega

/-- Every local factor of the admissible quadruple `{0,2,6,8}` is strictly positive. -/
theorem localFactor_pos_quad (p : ℕ) : 0 < localFactor ({0, 2, 6, 8} : Finset ℕ) p := by
  refine localFactor_pos_of_lt _ _ (fun hp => ?_)
  have hp2 := hp.two_le
  have hle : nu ({0, 2, 6, 8} : Finset ℕ) p ≤ 4 :=
    le_trans Finset.card_image_le (by decide)
  rcases Nat.lt_or_ge p 5 with hlt | hge
  · interval_cases p <;> decide
  · omega

end BrockianFrontier.SingularSeries

