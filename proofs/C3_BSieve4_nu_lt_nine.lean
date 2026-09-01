import Mathlib
namespace C3.BSieve4
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ := if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- The 9-tuple `{0,2,6,8,12,18,20,26,30}` is admissible: for every prime `p` it omits at
least one residue class mod `p`. For `p ≥ 11` this is immediate from the cardinality bound,
and the small primes `2,3,5,7` are checked by computation. -/
theorem nu_lt_nine (p : ℕ) (hp : p.Prime) :
    nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p < p := by
  by_cases h : p < 10
  · interval_cases p <;> simp_all (config := {decide := true})
  · push_neg at h
    calc nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p
        ≤ ({0,2,6,8,12,18,20,26,30} : Finset ℕ).card := Finset.card_image_le
      _ = 9 := by decide
      _ < p := by omega

theorem lf_pos_nine (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p := by
  unfold lF
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hp0 : (0:ℝ) < p := by linarith
    have hnum : 0 < 1 - (nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p : ℝ)/p := by
      have h1 := nu_lt_nine p hp
      have h2 : ((nu ({0,2,6,8,12,18,20,26,30} : Finset ℕ) p : ℝ)) < p := by exact_mod_cast h1
      rw [sub_pos, div_lt_one hp0]
      exact h2
    have hden : 0 < (1 - 1/(p:ℝ))^({0,2,6,8,12,18,20,26,30} : Finset ℕ).card := by
      apply pow_pos
      have : 1/(p:ℝ) ≤ 1/2 := by
        apply div_le_div_of_nonneg_left <;> linarith
      linarith
    exact div_pos hnum hden
  · norm_num

theorem adm_count_17 (g : ZMod 17) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 17 => r ≠ 0 ∧ r ≠ -g)).card = 15 := by
  revert hg
  revert g
  decide

theorem adm_count_19 (g : ZMod 19) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 19 => r ≠ 0 ∧ r ≠ -g)).card = 17 := by
  revert hg
  revert g
  decide

end C3.BSieve4

