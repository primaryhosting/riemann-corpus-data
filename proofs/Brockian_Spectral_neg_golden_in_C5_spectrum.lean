/-
  Brockian/Spectral.lean — the spectral face of the Brockian Pentagonal Law.

  Flagship: **`golden_unique_to_five`** — among the primes, the golden value
  `φ − 1` (`= 2 cos(2π/5)`) lies in the adjacency spectrum of the cycle graph
  `C_p` for *exactly one* prime, `p = 5`.

  We do NOT go through `SimpleGraph` (Mathlib 4.32 has no cycle-graph spectral
  API). Instead the spectrum is formalized CONCRETELY as the circulant/adjacency
  eigenvalues `2 cos(2πk/n)` of the `n`-cycle. The file is self-contained over
  Mathlib: the two pentagon cosine facts are proved inline from
  `Real.cos_pi_div_five : cos(π/5) = (1 + √5)/4`.

  Contents:
    * `cycleSpectrum n`                — the concrete eigenvalue set of `C_n`.
    * `cos_two_pi_div_five`            — `cos(2π/5) = (√5 − 1)/4`.
    * `two_cos_four_pi_div_five`       — `2 cos(4π/5) = −φ`.
    * `golden_sub_one_eq_two_cos`      — `φ − 1 = 2 cos(2π/5)` (the bridge fact).
    * `golden_in_cycleSpectrum_five`   — `φ − 1 ∈ spec(C₅)` (witness `k = 1`).
    * `neg_golden_in_C5_spectrum`      — `−φ ∈ spec(C₅)` (witness `k = 2`, angle `4π/5`).
    * `golden_unique_to_five`          — **the full iff**: for prime `p`,
                                          `φ − 1 ∈ spec(C_p) ↔ p = 5`.

  The `←` direction is the `k = 1` witness. The `→` direction uses
  `Real.cos_eq_cos_iff`: `cos(2πk/p) = cos(2π/5)` forces `2πk/p = ±2π/5 + 2πm`,
  i.e. `5k = p(5m ± 1)`, whence `5 ∣ p` (read mod 5), so the prime `p = 5`.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Brockian.Spectral

/-! ### The concrete cycle spectrum -/

/-- **The adjacency spectrum of the cycle graph `C_n`.** The `n × n` adjacency
matrix of the `n`-cycle is a circulant, so its eigenvalues are exactly
`2 cos(2πk/n)` for `k = 0, …, n−1`. We take this closed form as the definition,
sidestepping the (absent in Mathlib 4.32) cycle-graph spectral API. -/
def cycleSpectrum (n : ℕ) : Set ℝ :=
  {μ | ∃ k : ℕ, μ = 2 * Real.cos (2 * Real.pi * k / n)}

/-! ### The pentagon cosines (inline, from `Real.cos_pi_div_five`) -/

/-- **`cos(2π/5) = (√5 − 1)/4`.** Double-angle of `cos(π/5) = (1+√5)/4`. -/
theorem cos_two_pi_div_five :
    Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have hdiv : (2 * Real.pi / 5) = 2 * (Real.pi / 5) := by ring
  have htwo : Real.cos (2 * (Real.pi / 5)) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
    simpa using Real.cos_two_mul (Real.pi / 5)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [hdiv, htwo, hcos]
  ring_nf
  ring_nf at h5
  rw [h5]
  ring

/-- **`2 cos(4π/5) = −φ`.** Since `cos(4π/5) = −cos(π/5) = −(1+√5)/4` and
`φ = (1+√5)/2`, the `k = 2` eigenvalue of `C₅` is `−φ`. -/
theorem two_cos_four_pi_div_five :
    2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio := by
  have hcos : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have h : (4 * Real.pi / 5) = Real.pi - Real.pi / 5 := by ring
  have hg : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  rw [h, Real.cos_pi_sub, hcos, hg]
  ring

/-! ### The golden bridge fact -/

/-- **`φ − 1 = 2 cos(2π/5)`.** The golden value is twice the pentagon cosine. -/
theorem golden_sub_one_eq_two_cos :
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) := by
  have hg : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  rw [cos_two_pi_div_five, hg]
  ring

/-! ### Membership witnesses -/

/-- **`φ − 1 ∈ spec(C₅)`.** Witness `k = 1`: `2 cos(2π·1/5) = 2 cos(2π/5) = φ − 1`. -/
theorem golden_in_cycleSpectrum_five :
    (Real.goldenRatio - 1) ∈ cycleSpectrum 5 := by
  refine ⟨1, ?_⟩
  have h : 2 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))
      = Real.goldenRatio - 1 := by
    rw [golden_sub_one_eq_two_cos]; congr 2; push_cast; ring
  exact h.symm

/-- **`−φ ∈ spec(C₅)`.** Witness `k = 2`: `2 cos(2π·2/5) = 2 cos(4π/5) = −φ`. -/
theorem neg_golden_in_C5_spectrum :
    (-Real.goldenRatio) ∈ cycleSpectrum 5 := by
  refine ⟨2, ?_⟩
  have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 4 * Real.pi / 5 := by
    push_cast; ring
  rw [harg, two_cos_four_pi_div_five]

/-! ### The flagship uniqueness theorem -/

/-- **`golden_unique_to_five` — the pentagon is spectrally forced.**
For any prime `p`, the golden value `φ − 1` is an adjacency eigenvalue of the
cycle `C_p` **iff** `p = 5`.

`←` : the `k = 1` witness (`golden_in_cycleSpectrum_five`).
`→` : if `φ − 1 = 2 cos(2πk/p)` then `cos(2πk/p) = cos(2π/5)`, so by
`Real.cos_eq_cos_iff` there is `m : ℤ` with `2πk/p = 2πm ± 2π/5`, i.e.
`5k = p(5m ± 1)`. Reducing mod 5 gives `5 ∣ p`, and a prime divisible by 5 is 5. -/
theorem golden_unique_to_five {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1) ∈ cycleSpectrum p ↔ p = 5 := by
  constructor
  · rintro ⟨k, hk⟩
    -- hk : Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi * ↑k / ↑p)
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
    have h2pi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    -- reduce to a cosine equality
    have hcos : Real.cos (2 * Real.pi / 5)
        = Real.cos (2 * Real.pi * (k : ℝ) / (p : ℝ)) := by
      have h2 : (2 : ℝ) * Real.cos (2 * Real.pi / 5)
          = 2 * Real.cos (2 * Real.pi * (k : ℝ) / (p : ℝ)) := by
        rw [← golden_sub_one_eq_two_cos]; exact hk
      linarith
    rw [Real.cos_eq_cos_iff] at hcos
    obtain ⟨m, hm | hm⟩ := hcos
    · -- 2πk/p = 2mπ + 2π/5
      rw [div_eq_iff hpR] at hm
      have hstep : 2 * Real.pi * (k : ℝ)
          = 2 * Real.pi * (((m : ℝ) + 1 / 5) * (p : ℝ)) := by
        linear_combination hm
      have hk2 : (k : ℝ) = ((m : ℝ) + 1 / 5) * (p : ℝ) :=
        mul_left_cancel₀ h2pi hstep
      have hreal : (5 : ℝ) * (k : ℝ) = (p : ℝ) * (5 * (m : ℝ) + 1) := by
        linear_combination 5 * hk2
      have hz : (5 : ℤ) * (k : ℤ) = (p : ℤ) * (5 * m + 1) := by exact_mod_cast hreal
      have hdvd : (5 : ℤ) ∣ (p : ℤ) := ⟨(k : ℤ) - (p : ℤ) * m, by linear_combination -hz⟩
      have h5p : (5 : ℕ) ∣ p := by exact_mod_cast hdvd
      exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5p).symm
    · -- 2πk/p = 2mπ - 2π/5
      rw [div_eq_iff hpR] at hm
      have hstep : 2 * Real.pi * (k : ℝ)
          = 2 * Real.pi * (((m : ℝ) - 1 / 5) * (p : ℝ)) := by
        linear_combination hm
      have hk2 : (k : ℝ) = ((m : ℝ) - 1 / 5) * (p : ℝ) :=
        mul_left_cancel₀ h2pi hstep
      have hreal : (5 : ℝ) * (k : ℝ) = (p : ℝ) * (5 * (m : ℝ) - 1) := by
        linear_combination 5 * hk2
      have hz : (5 : ℤ) * (k : ℤ) = (p : ℤ) * (5 * m - 1) := by exact_mod_cast hreal
      have hdvd : (5 : ℤ) ∣ (p : ℤ) := ⟨(p : ℤ) * m - (k : ℤ), by linear_combination hz⟩
      have h5p : (5 : ℕ) ∣ p := by exact_mod_cast hdvd
      exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5p).symm
  · rintro rfl
    exact golden_in_cycleSpectrum_five

end Brockian.Spectral
