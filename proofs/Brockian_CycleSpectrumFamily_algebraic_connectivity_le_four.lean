/-
  Brockian/CycleSpectrumFamily.lean — cycle-adjacency spectrum for general C_n.

  Generalizes the concrete circulant spectrum already used in
  `Brockian.Spectral` / `Brockian.Connectivity` without numerology.

  The adjacency eigenvalues of the n-cycle are formalized as
  `cycleSpectrum n = { 2 cos(2πk/n) | k ∈ ℕ }` (definition from Spectral.lean).
  This file records the universal bounds, the k = 1 mode, explicit spectra for
  small regular polygons n = 3, 4, 6, the Laplacian / algebraic-connectivity
  formulas, and the *existing* C₅ golden comparison via `golden_unique_to_five`.

  Honesty boundary: the only prime-cycle rigidity claimed for φ − 1 is exactly
  what `golden_unique_to_five` already says (among primes, φ − 1 ∈ spec(C_p)
  iff p = 5). No claim that only n = 5 is “cosmic.”

  Contents:
    * spectrum membership / definition recap
    * λ_max(C_n) = 2; spectrum ⊆ [−2, 2]; k = 1 eigenvalue 2 cos(2π/n)
    * explicit spectrum values for C₃, C₄, C₆
    * golden comparison: C₅ via golden_unique_to_five
    * Laplacian spectrum + algebraic connectivity λ₂ = 2 − 2 cos(2π/n)

  Verification: no sorry; AXLE when attested.
-/
import Mathlib
import Brockian.Spectral
import Brockian.Connectivity

namespace Brockian.CycleSpectrumFamily

open Brockian.Spectral
open Real

/-! ### Spectrum membership corollaries -/

/-- Every circulant mode `2 cos(2πk/n)` is an adjacency eigenvalue of `C_n`. -/
theorem mem_cycleSpectrum (n k : ℕ) :
    2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) ∈ cycleSpectrum n :=
  ⟨k, rfl⟩

/-- The k = 0 mode is the constant eigenvector eigenvalue `2`. -/
theorem two_mem_cycleSpectrum (n : ℕ) : (2 : ℝ) ∈ cycleSpectrum n := by
  refine ⟨0, ?_⟩
  simp [Real.cos_zero]

/-- The fundamental mode k = 1: eigenvalue `2 cos(2π/n)`. -/
theorem cycle_eig_one (n : ℕ) :
    2 * Real.cos (2 * Real.pi / n) ∈ cycleSpectrum n := by
  refine ⟨1, ?_⟩
  congr 2
  push_cast
  ring

/-- Every adjacency eigenvalue of `C_n` is at most `2` (since cos ≤ 1). -/
theorem cycleSpectrum_le_two {n : ℕ} {μ : ℝ} (hμ : μ ∈ cycleSpectrum n) : μ ≤ 2 := by
  obtain ⟨k, rfl⟩ := hμ
  have hcos : Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) ≤ 1 := Real.cos_le_one _
  linarith

/-- Every adjacency eigenvalue of `C_n` is at least `−2` (since cos ≥ −1). -/
theorem cycleSpectrum_ge_neg_two {n : ℕ} {μ : ℝ}
    (hμ : μ ∈ cycleSpectrum n) : (-2 : ℝ) ≤ μ := by
  obtain ⟨k, rfl⟩ := hμ
  have hcos : (-1 : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) := Real.neg_one_le_cos _
  linarith

/-- **λ_max(C_n) = 2.**  The value `2` is attained (k = 0) and is an upper bound
for the whole spectrum. -/
theorem lambda_max_cycle (n : ℕ) :
    (2 : ℝ) ∈ cycleSpectrum n ∧ ∀ μ ∈ cycleSpectrum n, μ ≤ 2 :=
  ⟨two_mem_cycleSpectrum n, fun _ h => cycleSpectrum_le_two h⟩

/-- Spectrum of the cycle adjacency lies in the closed interval `[-2, 2]`. -/
theorem cycleSpectrum_subset_Icc (n : ℕ) :
    cycleSpectrum n ⊆ Set.Icc (-2 : ℝ) 2 := by
  intro μ hμ
  exact ⟨cycleSpectrum_ge_neg_two hμ, cycleSpectrum_le_two hμ⟩

/-! ### Explicit spectra: C₃, C₄, C₆ -/

/-- Helper: `cos(2π/3) = −1/2`. -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = (-1 : ℝ) / 2 := by
  have h : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

/-- Helper: `cos(4π/3) = −1/2`. -/
theorem cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = (-1 : ℝ) / 2 := by
  have h : (4 * Real.pi / 3 : ℝ) = Real.pi + Real.pi / 3 := by ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  ring

/-- Helper: `2 cos(2π/3) = −1`. -/
theorem two_cos_two_pi_div_three : 2 * Real.cos (2 * Real.pi / 3) = (-1 : ℝ) := by
  rw [cos_two_pi_div_three]; ring

/-- Helper: `2 cos(π/3) = 1`. -/
theorem two_cos_pi_div_three : 2 * Real.cos (Real.pi / 3) = (1 : ℝ) := by
  rw [Real.cos_pi_div_three]; ring

/-- **C₃ spectrum values.**  Eigenvalues: `2` (k=0), `−1` (k=1,2). -/
theorem cycle3_eig_zero : (2 : ℝ) ∈ cycleSpectrum 3 := two_mem_cycleSpectrum 3

theorem cycle3_eig_one : (-1 : ℝ) ∈ cycleSpectrum 3 := by
  refine ⟨1, ?_⟩
  have harg : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 2 * Real.pi / 3 := by
    push_cast; ring
  rw [harg, two_cos_two_pi_div_three]

theorem cycle3_eig_two : (-1 : ℝ) ∈ cycleSpectrum 3 := by
  refine ⟨2, ?_⟩
  have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = 4 * Real.pi / 3 := by
    push_cast; ring
  rw [harg, cos_four_pi_div_three]
  ring

/-- **C₄ spectrum values.**  Eigenvalues: `2`, `0`, `−2`, `0`. -/
theorem cycle4_eig_zero : (2 : ℝ) ∈ cycleSpectrum 4 := two_mem_cycleSpectrum 4

theorem cycle4_eig_one : (0 : ℝ) ∈ cycleSpectrum 4 := by
  refine ⟨1, ?_⟩
  have harg : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = Real.pi / 2 := by
    push_cast; ring
  rw [harg, Real.cos_pi_div_two]
  ring

theorem cycle4_eig_two : (-2 : ℝ) ∈ cycleSpectrum 4 := by
  refine ⟨2, ?_⟩
  have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = Real.pi := by
    push_cast; ring
  rw [harg, Real.cos_pi]
  ring

theorem cycle4_eig_three : (0 : ℝ) ∈ cycleSpectrum 4 := by
  refine ⟨3, ?_⟩
  have harg : 2 * Real.pi * ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 3 * Real.pi / 2 := by
    push_cast; ring
  -- cos(3π/2) = cos(π + π/2) = −cos(π/2) = 0
  have h : (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 := by ring
  rw [harg, h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

/-- **C₆ spectrum values.**  Eigenvalues: `2`, `1`, `−1`, `−2`, `−1`, `1`. -/
theorem cycle6_eig_zero : (2 : ℝ) ∈ cycleSpectrum 6 := two_mem_cycleSpectrum 6

theorem cycle6_eig_one : (1 : ℝ) ∈ cycleSpectrum 6 := by
  refine ⟨1, ?_⟩
  have harg : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi / 3 := by
    push_cast; ring
  rw [harg, two_cos_pi_div_three]

theorem cycle6_eig_two : (-1 : ℝ) ∈ cycleSpectrum 6 := by
  refine ⟨2, ?_⟩
  have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 2 * Real.pi / 3 := by
    push_cast; ring
  rw [harg, two_cos_two_pi_div_three]

theorem cycle6_eig_three : (-2 : ℝ) ∈ cycleSpectrum 6 := by
  refine ⟨3, ?_⟩
  have harg : 2 * Real.pi * ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = Real.pi := by
    push_cast; ring
  rw [harg, Real.cos_pi]
  ring

theorem cycle6_eig_four : (-1 : ℝ) ∈ cycleSpectrum 6 := by
  refine ⟨4, ?_⟩
  have harg : 2 * Real.pi * ((4 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 4 * Real.pi / 3 := by
    push_cast; ring
  rw [harg, cos_four_pi_div_three]
  ring

theorem cycle6_eig_five : (1 : ℝ) ∈ cycleSpectrum 6 := by
  refine ⟨5, ?_⟩
  have harg : 2 * Real.pi * ((5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 5 * Real.pi / 3 := by
    push_cast; ring
  -- cos(5π/3) = cos(2π − π/3) = cos(π/3) = 1/2
  have h : (5 * Real.pi / 3 : ℝ) = 2 * Real.pi - Real.pi / 3 := by ring
  rw [harg, h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_three]
  ring

/-! ### Golden comparison (C₅ only — cites existing uniqueness) -/

/-- **φ − 1 is an adjacency eigenvalue of C₅.**  Direct restatement of the
`k = 1` witness already proved in Spectral.lean. -/
theorem golden_in_C5 : (Real.goldenRatio - 1) ∈ cycleSpectrum 5 :=
  golden_in_cycleSpectrum_five

/-- **Among primes, φ − 1 appears in the cycle spectrum exactly at p = 5.**
This is *exactly* `golden_unique_to_five` — no stronger cosmic claim. -/
theorem golden_unique_among_prime_cycles {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1) ∈ cycleSpectrum p ↔ p = 5 :=
  golden_unique_to_five hp

/-- **−φ is also a C₅ adjacency eigenvalue** (the k = 2 mode). -/
theorem neg_golden_in_C5 : (-Real.goldenRatio) ∈ cycleSpectrum 5 :=
  neg_golden_in_C5_spectrum

/-- The fundamental C₅ eigenvalue equals φ − 1:
`2 cos(2π/5) = φ − 1`. -/
theorem two_cos_two_pi_div_five_eq_golden_sub_one :
    2 * Real.cos (2 * Real.pi / 5) = Real.goldenRatio - 1 :=
  golden_sub_one_eq_two_cos.symm

/-! ### Laplacian spectrum and algebraic connectivity -/

/-- Concrete Laplacian spectrum of the n-cycle (2-regular ⇒ L = 2I − A):
`{ 2 − 2 cos(2πk/n) | k ∈ ℕ }`. -/
def laplacianCycleSpectrum (n : ℕ) : Set ℝ :=
  {μ | ∃ k : ℕ, μ = 2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))}

/-- Each Laplacian mode is present. -/
theorem mem_laplacianCycleSpectrum (n k : ℕ) :
    2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) ∈ laplacianCycleSpectrum n :=
  ⟨k, rfl⟩

/-- Trivial Laplacian eigenvalue `0` (k = 0). -/
theorem zero_mem_laplacianCycleSpectrum (n : ℕ) :
    (0 : ℝ) ∈ laplacianCycleSpectrum n := by
  refine ⟨0, ?_⟩
  simp [Real.cos_zero]

/-- **Algebraic connectivity formula (membership).**
For any n, the second-smallest Laplacian eigenvalue of C_n is the k = 1 mode
`2 − 2 cos(2π/n)` (standard graph-theory fact for the cycle; we record membership
and the elementary positivity / bound facts below). -/
theorem algebraic_connectivity_mem (n : ℕ) :
    2 - 2 * Real.cos (2 * Real.pi / n) ∈ laplacianCycleSpectrum n := by
  refine ⟨1, ?_⟩
  congr 2
  push_cast
  ring

/-- For `n ≥ 3`, the angle `2π/n` lies in `(0, 2π)`, so `cos(2π/n) < 1` and thus
the algebraic connectivity is strictly positive. -/
theorem algebraic_connectivity_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < 2 - 2 * Real.cos (2 * Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) hn)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hn)
  have hθ_pos : 0 < 2 * Real.pi / (n : ℝ) := by positivity
  have hlt2π : 2 * Real.pi / (n : ℝ) < 2 * Real.pi := by
    rw [div_lt_iff₀ hn0]
    -- 2π < 2π · n  since n > 1 and π > 0
    nlinarith [Real.pi_pos, hn1]
  -- On `(-(2π), 2π)`, `cos θ = 1` iff `θ = 0`; our angle is strictly positive, so cos < 1.
  have hcos : Real.cos (2 * Real.pi / n) < 1 := by
    have hne : Real.cos (2 * Real.pi / n) ≠ 1 := by
      intro heq
      have hiff :=
        (Real.cos_eq_one_iff_of_lt_of_lt
          (by nlinarith [Real.pi_pos, hθ_pos] : -(2 * Real.pi) < 2 * Real.pi / (n : ℝ))
          hlt2π).mp heq
      exact (ne_of_gt hθ_pos) hiff
    exact lt_of_le_of_ne (Real.cos_le_one _) hne
  linarith

/-- Laplacian eigenvalues of a 2-regular graph are at most `4`
(`2 − 2 cos ≤ 2 − 2(−1) = 4`). -/
theorem laplacianCycleSpectrum_le_four {n : ℕ} {μ : ℝ}
    (hμ : μ ∈ laplacianCycleSpectrum n) : μ ≤ 4 := by
  obtain ⟨k, rfl⟩ := hμ
  have hcos : (-1 : ℝ) ≤ Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) := Real.neg_one_le_cos _
  linarith

/-- Algebraic connectivity is at most 4 (degree-bound style). -/
theorem algebraic_connectivity_le_four (n : ℕ) :
    2 - 2 * Real.cos (2 * Real.pi / n) ≤ 4 :=
  laplacianCycleSpectrum_le_four (algebraic_connectivity_mem n)

/-- Nonnegativity of Laplacian modes (cos ≤ 1 ⇒ 2 − 2 cos ≥ 0). -/
theorem laplacianCycleSpectrum_nonneg {n : ℕ} {μ : ℝ}
    (hμ : μ ∈ laplacianCycleSpectrum n) : 0 ≤ μ := by
  obtain ⟨k, rfl⟩ := hμ
  have hcos : Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) ≤ 1 := Real.cos_le_one _
  linarith

/-- **C₅ algebraic connectivity specializes to `2 − 1/φ`.**
Cites the Connectivity identity `lambda2_eq`. -/
theorem algebraic_connectivity_five :
    2 - 2 * Real.cos (2 * Real.pi / 5) = 2 - 1 / Real.goldenRatio :=
  Brockian.Connectivity.lambda2_eq

/-- C₅ algebraic connectivity is positive and equals `2 − 1/φ`, as recorded by
`Connectivity.pentagon_lambda2_phi` (membership + positivity + ordering). -/
theorem algebraic_connectivity_five_props :
    (2 - 1 / Real.goldenRatio) ∈ Brockian.Connectivity.laplacianEigs5 ∧
    0 < 2 - 1 / Real.goldenRatio ∧
    (2 - 1 / Real.goldenRatio) ≤ 2 - 2 * Real.cos (4 * Real.pi / 5) :=
  Brockian.Connectivity.pentagon_lambda2_phi

end Brockian.CycleSpectrumFamily
