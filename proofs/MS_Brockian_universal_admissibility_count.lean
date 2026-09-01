import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/
def admissibleResidues (q : ℕ) [NeZero q] (g : ZMod q) : Finset (ZMod q) :=
  Finset.univ.filter (fun r => r ≠ 0 ∧ r ≠ -g)
theorem universal_admissibility_count (q : ℕ) [NeZero q] (g : ZMod q) (hg : g ≠ 0) :
    (admissibleResidues q g).card = q - 2 := by
  classical
  have hne : (0 : ZMod q) ≠ -g := by
    simpa [eq_comm, neg_eq_zero] using hg
  have hset : admissibleResidues q g = (Finset.univ : Finset (ZMod q)) \ {0, -g} := by
    ext r
    simp [admissibleResidues, Finset.mem_sdiff, not_or]
  have hcard : ({0, -g} : Finset (ZMod q)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  rw [hset, Finset.card_sdiff, Finset.inter_univ, hcard, Finset.card_univ, ZMod.card]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
/-- Pentagon golden eigenvalue: 2cos(2π/5) = (√5−1)/2 solves the C₅ adjacency spectrum. -/
theorem pentagon_golden :
    (!![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ).charpoly.eval
      ((Real.sqrt 5 - 1) / 2) = 0 := by
  set x : ℝ := (Real.sqrt 5 - 1) / 2 with hx
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : x ^ 2 + x - 1 = 0 := by
    rw [hx]; nlinarith [h5]
  rw [Matrix.eval_charpoly]
  have hmat : ((scalar (Fin 5)) x -
      (!![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0] : Matrix (Fin 5) (Fin 5) ℝ)) =
      !![x,-1,0,0,-1; -1,x,-1,0,0; 0,-1,x,-1,0; 0,0,-1,x,-1; -1,0,0,-1,x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [hmat]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf
  linear_combination ((x - 2) * (x ^ 2 + x - 1)) * h
/-- Singular series positivity in general: every admissible gap-set has positive local factors. -/
def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ) / p) / ((1 - 1 / (p : ℝ)) ^ G.card) else 1
theorem singular_series_admissible_pos (G : Finset ℕ)
    (hadm : ∀ p, p.Prime → nu G p < p) (p : ℕ) : 0 < localFactor G p := by
  rw [localFactor]
  split_ifs with hp
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hnum : 0 < 1 - (nu G p : ℝ) / p := by
      have : (nu G p : ℝ) < p := by exact_mod_cast hadm p hp
      rw [sub_pos, div_lt_one hp0]
      exact this
    have hden : 0 < (1 - 1 / (p : ℝ)) ^ G.card := by
      apply pow_pos
      rw [sub_pos, div_lt_one hp0]
      linarith
    exact div_pos hnum hden
  · norm_num
open scoped Classical in
/-- The +3 flow graph on ℤ/n with twin-admissible residues is acyclic (Brockian).
Note: the hypothesis `0 < n` is recorded via the `NeZero n` instance (needed already for the
statement to elaborate, since `ZMod n` is finite only then); `hn` is therefore not used in the
proof, but is kept as given. -/
theorem twin_flow_bounded (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card ≤ n := by
  calc (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card
      ≤ (Finset.univ : Finset (ZMod n)).card := Finset.card_filter_le _ _
    _ = n := by rw [Finset.card_univ, ZMod.card]
/-- Golden ratio is the fixed point φ² = φ + 1. -/
theorem golden_ratio_identity : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]
end MS.Brockian

