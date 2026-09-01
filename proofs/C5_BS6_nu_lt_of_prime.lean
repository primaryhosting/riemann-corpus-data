import Mathlib
namespace C5.BS6
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ := if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- The 11-tuple `{0,2,6,8,12,18,20,26,30,32,36}` is admissible: for every prime `p`
it omits at least one residue class mod `p`. -/
theorem nu_lt_of_prime (p : ℕ) (hp : p.Prime) :
    nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p < p := by
  rcases lt_or_ge p 12 with h | h
  · have h2 := hp.two_le
    interval_cases p <;> simp_all (decide := true)
  · calc nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p
        ≤ ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ).card := Finset.card_image_le
      _ = 11 := by decide
      _ < p := by omega

theorem lf_pos_11 (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p := by
  rw [lF]
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hppos : (0:ℝ) < (p:ℝ) := by linarith
    have hnu : nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p < p := nu_lt_of_prime p hp
    have hnuR : (nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p : ℝ) < (p:ℝ) := by
      exact_mod_cast hnu
    apply div_pos
    · have : (nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p : ℝ) / (p:ℝ) < 1 :=
        (div_lt_one hppos).mpr hnuR
      linarith
    · apply pow_pos
      have : 1 / (p:ℝ) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le <;> linarith
      linarith
  · norm_num

theorem adm_29 (g : ZMod 29) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 29 => r ≠ 0 ∧ r ≠ -g)).card = 27 := by
  revert g
  decide

theorem adm_31 (g : ZMod 31) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 31 => r ≠ 0 ∧ r ≠ -g)).card = 29 := by
  revert g
  decide

end C5.BS6

