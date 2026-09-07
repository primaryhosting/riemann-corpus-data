import Mathlib

namespace Brockian.FareySeparation

open Finset

/-- Distance from `x` to the nearest integer, i.e. `‖x‖` on ℝ/ℤ. -/
noncomputable def distZ (x : ℝ) : ℝ := |x - round x|

/-- `X` is `δ`-separated modulo 1. -/
def IsSeparated (X : Finset ℝ) (δ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ distZ (x - y)

/-- The Farey fractions `b/q` with `q ≤ Q` and `gcd(b,q) = 1`. -/
noncomputable def fareySet (Q : ℕ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion fun q =>
    ((Finset.range q).filter fun b => Nat.Coprime b q).image (fun b : ℕ => (b : ℝ) / (q : ℝ))

/-- Farey fractions of order `Q` are `Q⁻²`-separated. -/
theorem farey_separated (Q : ℕ) (hQ : 0 < Q) :
    IsSeparated (fareySet Q) ((Q : ℝ) ^ 2)⁻¹ := by
  intro x hx y hy hxy
  simp only [fareySet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc] at hx hy
  obtain ⟨q, ⟨hq1, hqQ⟩, b, ⟨hbq, hcop⟩, hxeq⟩ := hx
  obtain ⟨q', ⟨hq1', hqQ'⟩, b', ⟨hbq', hcop'⟩, hyeq⟩ := hy
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqpos' : (0 : ℝ) < q' := by exact_mod_cast hq1'
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hqne' : (q' : ℝ) ≠ 0 := ne_of_gt hqpos'
  subst hxeq
  subst hyeq
  -- Set up the difference `d`.
  set d : ℝ := (b : ℝ) / q - (b' : ℝ) / q' with hddef
  -- Both fractions lie in [0,1), so `d ∈ (-1, 1)`.
  have hx0 : 0 ≤ (b : ℝ) / q := by positivity
  have hy0 : 0 ≤ (b' : ℝ) / q' := by positivity
  have hx1 : (b : ℝ) / q < 1 := (div_lt_one hqpos).mpr (by exact_mod_cast hbq)
  have hy1 : (b' : ℝ) / q' < 1 := (div_lt_one hqpos').mpr (by exact_mod_cast hbq')
  have hd_lt : d < 1 := by rw [hddef]; linarith
  have hd_gt : (-1 : ℝ) < d := by rw [hddef]; linarith
  -- The core integer: numerator of `d - round d` over `q q'`.
  set m : ℤ := (b : ℤ) * (q' : ℤ) - (b' : ℤ) * (q : ℤ) - (round d) * ((q : ℤ) * (q' : ℤ))
    with hmdef
  have hcast : (m : ℝ) = (b : ℝ) * q' - (b' : ℝ) * q - (round d : ℝ) * ((q : ℝ) * q') := by
    rw [hmdef]; push_cast; ring
  have hid : d - (round d : ℝ) = (m : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    rw [hcast, hddef]; field_simp
  -- `d - round d ≠ 0`, because `d ∈ (-1,1)` and `d ≠ 0`.
  have hdnz : d - (round d : ℝ) ≠ 0 := by
    intro h
    have hR_lt : (round d : ℝ) < 1 := by linarith
    have hR_gt : (-1 : ℝ) < (round d : ℝ) := by linarith
    have hz : round d = 0 := by
      have c1 : round d < 1 := by exact_mod_cast hR_lt
      have c2 : (-1 : ℤ) < round d := by exact_mod_cast hR_gt
      omega
    rw [hz, Int.cast_zero, sub_zero] at h
    rw [hddef] at h
    apply hxy
    linarith
  -- Hence `m ≠ 0`, so `|m| ≥ 1`.
  have hmne : m ≠ 0 := by
    intro hm0
    apply hdnz
    rw [hid, hm0]; simp
  have hint : (1 : ℤ) ≤ |m| := Int.one_le_abs hmne
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hint
  -- `distZ d = |m| / (q q')`.
  have hqqpos : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := by positivity
  have hdist : distZ d = |(m : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    simp only [distZ]
    rw [hid, abs_div, abs_of_pos hqqpos]
  -- `q q' ≤ Q²`.
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hqQR' : (q' : ℝ) ≤ Q := by exact_mod_cast hqQ'
  have hQ2pos : (0 : ℝ) < (Q : ℝ) ^ 2 := pow_pos hQpos 2
  have hQsq : (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have hmul := mul_le_mul hqQR hqQR' (le_of_lt hqpos') (le_of_lt hQpos)
    calc (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) * (Q : ℝ) := hmul
      _ = (Q : ℝ) ^ 2 := by ring
  -- Assemble the bound.
  have hfin : ((Q : ℝ) ^ 2)⁻¹ ≤ |(m : ℝ)| / ((q : ℝ) * (q' : ℝ)) := by
    have e1 : ((Q : ℝ) ^ 2)⁻¹ * ((q : ℝ) * (q' : ℝ)) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hQsq (le_of_lt (inv_pos.mpr hQ2pos))
      rwa [inv_mul_cancel₀ (ne_of_gt hQ2pos)] at h
    rw [le_div_iff₀ hqqpos]
    calc ((Q : ℝ) ^ 2)⁻¹ * ((q : ℝ) * (q' : ℝ)) ≤ 1 := e1
      _ ≤ |(m : ℝ)| := hm1
  rw [hdist]
  exact hfin

end Brockian.FareySeparation
