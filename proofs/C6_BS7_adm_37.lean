import Mathlib
namespace C6.BS7
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ := if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- For `g ≠ 0` in `ZMod 37`, exactly `35` residues avoid both `0` and `-g`:
the excluded set `{0, -g}` has two elements, and `37 - 2 = 35`. -/
theorem adm_37 (g : ZMod 37) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 37 => r ≠ 0 ∧ r ≠ -g)).card = 35 := by
  have h1 : (Finset.univ.filter (fun r : ZMod 37 => r ≠ 0 ∧ r ≠ -g))
      = ({0, -g} : Finset (ZMod 37))ᶜ := by
    ext r; simp
  have h2 : ({0, -g} : Finset (ZMod 37)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa [eq_comm, neg_eq_zero] using hg),
      Finset.card_singleton]
  rw [h1, Finset.card_compl, h2]
  simp

/-- The admissible 12-tuple `{0,2,6,8,12,18,20,26,30,32,36,42}` has positive local factor at
every `p`: for `p ≥ 13` the number of occupied residues is at most the size `12` of the tuple,
and for `p ∈ {2,3,5,7,11}` admissibility is checked by computation. -/
theorem lf_pos_12 (p : ℕ) : 0 < lF ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p := by
  rw [lF]
  split
  · rename_i hp
    have hp2 : 2 ≤ p := hp.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hnu : nu ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p < p := by
      by_cases h13 : 13 ≤ p
      · calc nu ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p
            ≤ ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ).card := Finset.card_image_le
          _ = 12 := by decide
          _ < p := by omega
      · interval_cases p <;> revert hp <;> decide
    have hnuR : (nu ({0,2,6,8,12,18,20,26,30,32,36,42} : Finset ℕ) p : ℝ) < (p:ℝ) := by
      exact_mod_cast hnu
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hnuR
    · exact pow_pos (by rw [sub_pos, div_lt_one (by linarith)]; linarith) _
  · norm_num

/-- A nonempty set of integers occupies at least one residue class mod `p`. -/
theorem nu_pos (G : Finset ℕ) (p : ℕ) (hG : G.Nonempty) : 0 < nu G p :=
  Finset.card_pos.mpr (hG.image _)
end C6.BS7

