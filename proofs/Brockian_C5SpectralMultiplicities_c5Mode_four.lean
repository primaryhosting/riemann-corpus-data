/-
  Brockian/C5SpectralMultiplicities.lean — C₅ adjacency spectrum *with multiplicities*.

  The set-level spectrum `Brockian.Spectral.cycleSpectrum 5` already records that
  the values `2`, `φ − 1`, and `−φ` appear as circulant eigenvalues.  This module
  packages the *finite multiset* of the five modes `k = 0,1,2,3,4`:

    k = 0        →  2                         (multiplicity 1)
    k = 1, 4     →  2 cos(2π/5) = φ − 1      (multiplicity 2)
    k = 2, 3     →  2 cos(4π/5) = −φ          (multiplicity 2)

  Multiplicity is formalized as `Multiset.count` of the concrete mode list, not as
  geometric eigenspace dimension (that operator-level story lives in
  `D5LaplacianModes` / Fourier modes).  The honest reading here is "algebraic
  multiplicity of circulant modes k = 0..4".

  Links (without overclaiming):
    * value identities cite `Spectral.golden_sub_one_eq_two_cos` /
      `Spectral.two_cos_four_pi_div_five` and Connectivity cosine facts;
    * set-level golden uniqueness remains `Spectral.golden_unique_to_five`
      (among primes, φ − 1 ∈ spec(C_p) iff p = 5) — multiplicity does not
      strengthen that uniqueness statement.

  Verification: no sorry; AXLE when attested.
-/
import Mathlib
import Brockian.Spectral
import Brockian.Connectivity
import Brockian.CycleSpectrumFamily

namespace Brockian.C5SpectralMultiplicities

open Brockian.Spectral
open Real

local notation "φ" => Real.goldenRatio

/-! ### Circulant modes of C₅ -/

/-- The k-th circulant adjacency mode of the 5-cycle: `2 cos(2πk/5)`. -/
noncomputable def c5Mode (k : ℕ) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℝ) / 5)

/-- The finite multiset of C₅ adjacency eigenvalues (one per mode `k = 0,…,4`). -/
noncomputable def c5SpectrumMultiset : Multiset ℝ :=
  {c5Mode 0, c5Mode 1, c5Mode 2, c5Mode 3, c5Mode 4}

/-- Distinct values appearing in the C₅ multiset (the support of the spectrum). -/
noncomputable def c5DistinctEigs : Finset ℝ :=
  {(2 : ℝ), φ - 1, -φ}

/-! ### Mode evaluations -/

/-- **Mode 0.**  `2 cos(0) = 2`. -/
theorem c5Mode_zero : c5Mode 0 = 2 := by
  simp [c5Mode, Real.cos_zero]

/-- Angle identity for mode 1: `2π·1/5 = 2π/5`. -/
theorem c5_arg_one : 2 * Real.pi * ((1 : ℕ) : ℝ) / 5 = 2 * Real.pi / 5 := by
  push_cast; ring

/-- Angle identity for mode 2: `2π·2/5 = 4π/5`. -/
theorem c5_arg_two : 2 * Real.pi * ((2 : ℕ) : ℝ) / 5 = 4 * Real.pi / 5 := by
  push_cast; ring

/-- Angle identity for mode 3: `2π·3/5 = 2π − 4π/5`. -/
theorem c5_arg_three : 2 * Real.pi * ((3 : ℕ) : ℝ) / 5 = 2 * Real.pi - 4 * Real.pi / 5 := by
  push_cast; ring

/-- Angle identity for mode 4: `2π·4/5 = 2π − 2π/5`. -/
theorem c5_arg_four : 2 * Real.pi * ((4 : ℕ) : ℝ) / 5 = 2 * Real.pi - 2 * Real.pi / 5 := by
  push_cast; ring

/-- **Mode 1.**  `2 cos(2π/5) = φ − 1`. -/
theorem c5Mode_one : c5Mode 1 = φ - 1 := by
  simp only [c5Mode]
  rw [c5_arg_one, golden_sub_one_eq_two_cos.symm]

/-- **Mode 2.**  `2 cos(4π/5) = −φ`. -/
theorem c5Mode_two : c5Mode 2 = -φ := by
  simp only [c5Mode]
  rw [c5_arg_two, two_cos_four_pi_div_five]

/-- **Mode 3.**  `2 cos(6π/5) = 2 cos(4π/5) = −φ` via `cos(2π − θ) = cos θ`. -/
theorem c5Mode_three : c5Mode 3 = -φ := by
  simp only [c5Mode]
  rw [c5_arg_three, Real.cos_two_pi_sub, two_cos_four_pi_div_five]

/-- **Mode 4.**  `2 cos(8π/5) = 2 cos(2π/5) = φ − 1`. -/
theorem c5Mode_four : c5Mode 4 = φ - 1 := by
  simp only [c5Mode]
  rw [c5_arg_four, Real.cos_two_pi_sub, golden_sub_one_eq_two_cos.symm]

/-- Modes 1 and 4 coincide (conjugate pair for angle 2π/5). -/
theorem c5Mode_one_eq_four : c5Mode 1 = c5Mode 4 := by
  rw [c5Mode_one, c5Mode_four]

/-- Modes 2 and 3 coincide (conjugate pair for angle 4π/5). -/
theorem c5Mode_two_eq_three : c5Mode 2 = c5Mode 3 := by
  rw [c5Mode_two, c5Mode_three]

/-! ### Multiset = {2, φ−1, −φ, −φ, φ−1} (up to order) -/

/-- Explicit expansion of the five-mode multiset. -/
theorem c5SpectrumMultiset_eq :
    c5SpectrumMultiset = {(2 : ℝ), φ - 1, -φ, -φ, φ - 1} := by
  simp only [c5SpectrumMultiset]
  rw [c5Mode_zero, c5Mode_one, c5Mode_two, c5Mode_three, c5Mode_four]

/-- The multiset has cardinality 5 (one eigenvalue per vertex / mode). -/
theorem c5SpectrumMultiset_card : Multiset.card c5SpectrumMultiset = 5 := by
  simp [c5SpectrumMultiset]

/-! ### Pairwise distinctness of the three values -/

/-- Helper: `φ < 2` from the golden quadratic and `1 < φ`. -/
theorem goldenRatio_lt_two : φ < 2 := by
  nlinarith [goldenRatio_sq, one_lt_goldenRatio]

/-- The three spectral values are pairwise distinct. -/
theorem c5_eigs_pairwise_distinct :
    (2 : ℝ) ≠ φ - 1 ∧ (2 : ℝ) ≠ -φ ∧ φ - 1 ≠ -φ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; linarith [goldenRatio_lt_two]
  · intro h; nlinarith [one_lt_goldenRatio]
  · intro h; nlinarith [one_lt_goldenRatio]

/-! ### Multiplicities via Multiset.count -/

private theorem ne_two_golden : (2 : ℝ) ≠ φ - 1 :=
  c5_eigs_pairwise_distinct.1

private theorem ne_two_neg_golden : (2 : ℝ) ≠ -φ :=
  c5_eigs_pairwise_distinct.2.1

private theorem ne_golden_neg_golden : φ - 1 ≠ -φ :=
  c5_eigs_pairwise_distinct.2.2

/-- **Multiplicity of 2 is 1** (the constant / Perron mode k = 0). -/
theorem multiplicity_two : Multiset.count (2 : ℝ) c5SpectrumMultiset = 1 := by
  rw [c5SpectrumMultiset_eq]
  simp [ne_two_golden, ne_two_neg_golden]

/-- **Multiplicity of φ − 1 is 2** (modes k = 1, 4). -/
theorem multiplicity_golden_sub_one :
    Multiset.count (φ - 1) c5SpectrumMultiset = 2 := by
  rw [c5SpectrumMultiset_eq]
  simp [ne_two_golden.symm, ne_golden_neg_golden]

/-- **Multiplicity of −φ is 2** (modes k = 2, 3). -/
theorem multiplicity_neg_golden :
    Multiset.count (-φ) c5SpectrumMultiset = 2 := by
  rw [c5SpectrumMultiset_eq]
  simp [ne_two_neg_golden.symm, ne_golden_neg_golden.symm]

/-- Every element of the multiset is one of the three distinct eigenvalues. -/
theorem mem_c5SpectrumMultiset_iff {μ : ℝ} :
    μ ∈ c5SpectrumMultiset ↔ μ = 2 ∨ μ = φ - 1 ∨ μ = -φ := by
  rw [c5SpectrumMultiset_eq]
  simp [Multiset.mem_cons, or_left_comm, or_comm]

/-! ### Support equals the three-value Finset -/

/-- The support (toFinset) of the multiset is exactly `{2, φ−1, −φ}`. -/
theorem c5SpectrumMultiset_toFinset :
    c5SpectrumMultiset.toFinset = c5DistinctEigs := by
  ext μ
  simp only [c5DistinctEigs, Finset.mem_insert, Finset.mem_singleton,
    Multiset.mem_toFinset, mem_c5SpectrumMultiset_iff]

/-- Cardinality of the distinct-eigenvalue set is 3. -/
theorem c5DistinctEigs_card : c5DistinctEigs.card = 3 := by
  have hd := c5_eigs_pairwise_distinct
  have h1 : (2 : ℝ) ∉ ({φ - 1, -φ} : Finset ℝ) := by
    simp [hd.1, hd.2.1]
  have h2 : φ - 1 ∉ ({-φ} : Finset ℝ) := by
    simp [hd.2.2]
  simp only [c5DistinctEigs]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_singleton]

/-! ### Link to set-level spectrum (no multiplicity claim beyond modes) -/

/-- Every multiset mode is a set-level eigenvalue (`∈ cycleSpectrum 5`). -/
theorem c5Mode_mem_cycleSpectrum (k : ℕ) : c5Mode k ∈ cycleSpectrum 5 :=
  ⟨k, rfl⟩

/-- The three distinct values all lie in `cycleSpectrum 5`. -/
theorem two_mem_C5 : (2 : ℝ) ∈ cycleSpectrum 5 :=
  CycleSpectrumFamily.two_mem_cycleSpectrum 5

theorem golden_sub_one_mem_C5 : (φ - 1) ∈ cycleSpectrum 5 :=
  golden_in_cycleSpectrum_five

theorem neg_golden_mem_C5 : (-φ) ∈ cycleSpectrum 5 :=
  neg_golden_in_C5_spectrum

/-- Restatement: among primes, φ − 1 appears in the *set-level* cycle spectrum
exactly at p = 5.  Multiplicity data above does **not** strengthen this; it only
counts modes inside C₅ itself. -/
theorem golden_unique_to_five_setlevel {p : ℕ} (hp : p.Prime) :
    (φ - 1) ∈ cycleSpectrum p ↔ p = 5 :=
  golden_unique_to_five hp

/-! ### Laplacian multiplicities (via L = 2I − A for 2-regular C₅) -/

/-- Laplacian mode `2 − λ_A` of the corresponding adjacency mode. -/
noncomputable def c5LapMode (k : ℕ) : ℝ :=
  2 - c5Mode k

/-- Finite multiset of Laplacian eigenvalues of C₅. -/
noncomputable def c5LaplacianMultiset : Multiset ℝ :=
  {c5LapMode 0, c5LapMode 1, c5LapMode 2, c5LapMode 3, c5LapMode 4}

theorem c5LapMode_zero : c5LapMode 0 = 0 := by
  simp [c5LapMode, c5Mode_zero]

theorem c5LapMode_one : c5LapMode 1 = 2 - (φ - 1) := by
  simp [c5LapMode, c5Mode_one]

theorem c5LapMode_two : c5LapMode 2 = 2 + φ := by
  simp [c5LapMode, c5Mode_two]

theorem c5LapMode_three : c5LapMode 3 = 2 + φ := by
  simp [c5LapMode, c5Mode_three]

theorem c5LapMode_four : c5LapMode 4 = 2 - (φ - 1) := by
  simp [c5LapMode, c5Mode_four]

/-- Explicit Laplacian multiset (mode order k = 0,1,2,3,4). -/
theorem c5LaplacianMultiset_eq :
    c5LaplacianMultiset =
      ({(0 : ℝ), 2 - (φ - 1), 2 + φ, 2 + φ, 2 - (φ - 1)} : Multiset ℝ) := by
  simp only [c5LaplacianMultiset]
  rw [c5LapMode_zero, c5LapMode_one, c5LapMode_two, c5LapMode_three, c5LapMode_four]

private theorem ne_zero_gap : (0 : ℝ) ≠ 2 - (φ - 1) := by
  intro h
  linarith [goldenRatio_lt_two]

private theorem ne_zero_large : (0 : ℝ) ≠ 2 + φ := by
  intro h
  nlinarith [one_lt_goldenRatio]

private theorem ne_gap_large : 2 - (φ - 1) ≠ 2 + φ := by
  intro h
  nlinarith [one_lt_goldenRatio]

/-- Laplacian multiplicity of 0 is 1. -/
theorem multiplicity_lap_zero : Multiset.count (0 : ℝ) c5LaplacianMultiset = 1 := by
  rw [c5LaplacianMultiset_eq]
  simp [ne_zero_gap, ne_zero_large]

/-- Algebraic-connectivity Laplacian value `2 − (φ − 1)` has multiplicity 2. -/
theorem multiplicity_lap_gap :
    Multiset.count (2 - (φ - 1)) c5LaplacianMultiset = 2 := by
  rw [c5LaplacianMultiset_eq]
  simp [ne_zero_gap.symm, ne_gap_large]

/-- The large Laplacian eigenvalue `2 + φ` has multiplicity 2. -/
theorem multiplicity_lap_large :
    Multiset.count (2 + φ) c5LaplacianMultiset = 2 := by
  rw [c5LaplacianMultiset_eq]
  simp [ne_zero_large.symm, ne_gap_large.symm]

/-- Connectivity identity: the gap eigenvalue equals `2 − 1/φ`. -/
theorem lap_gap_eq_connectivity :
    2 - (φ - 1) = 2 - 1 / φ := by
  have h : 1 / φ = φ - 1 := Brockian.Connectivity.one_div_phi
  rw [h]

/-- Packaging: multiplicity statement for the Connectivity algebraic gap. -/
theorem multiplicity_connectivity_gap :
    Multiset.count (2 - 1 / φ) c5LaplacianMultiset = 2 := by
  rw [← lap_gap_eq_connectivity]
  exact multiplicity_lap_gap

/-- The large Laplacian value equals `2 − (−φ)`. -/
theorem lap_large_eq : 2 - (-φ) = 2 + φ := by ring

/-- Alias: multiplicity of `2 + φ` (same as `multiplicity_lap_large`). -/
theorem multiplicity_lap_two_plus_phi :
    Multiset.count (2 + φ) c5LaplacianMultiset = 2 :=
  multiplicity_lap_large

end Brockian.C5SpectralMultiplicities
