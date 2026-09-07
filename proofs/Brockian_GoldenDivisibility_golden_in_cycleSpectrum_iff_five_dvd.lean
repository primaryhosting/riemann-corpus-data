/-
  Brockian/GoldenDivisibility.lean — the Golden Divisibility Law.

  The crown generalization of the pentagon uniqueness theorem
  `Brockian.Spectral.golden_unique_to_five` from primes to ALL cycles.

  Flagship: **`golden_in_cycleSpectrum_iff_five_dvd`** — for every `n ≥ 1`,
  the golden value `φ − 1` (`= 2 cos(2π/5)`) lies in the adjacency spectrum of
  the cycle graph `C_n` **iff `5 ∣ n`**.

  The pentagon `n = 5` is the smallest such cycle; every fifth cycle `C_{5j}`
  inherits the golden mode through its `k = j` eigenvector.

  * `→` : from `φ − 1 = 2 cos(2πk/n)` we get `cos(2πk/n) = cos(2π/5)`, so by
    `Real.cos_eq_cos_iff` there is `m : ℤ` with `2πk/n = 2πm ± 2π/5`, i.e.
    `5k = n(5m ± 1)`. Reduced over `ℤ` this yields `5 ∣ n` (no primality needed).
    This is the exact analytic chain of the prime proof, stopping one step earlier.
  * `←` : write `n = 5j` with `j ≥ 1`; the witness `k = j` gives angle
    `2π·j/(5j) = 2π/5`, so `2 cos(2π k/n) = 2 cos(2π/5) = φ − 1`.

  The prime uniqueness theorem is recovered as a corollary:
  `golden_unique_to_five_recovered` specializes `5 ∣ p ↔ p = 5` for prime `p`.

  Verification: AXLE @ lean-4.32.0; no sorry/native_decide/added axiom;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.Spectral
import Brockian.CycleSpectrumFamily

namespace Brockian.GoldenDivisibility

open Brockian

/-- **The Golden Divisibility Law.** For every `n ≥ 1`, the golden value `φ − 1`
is an adjacency eigenvalue of the cycle `C_n` **iff 5 divides n**. The pentagon
(`n = 5`) is the smallest such cycle; every fifth cycle inherits the golden mode.
The prime uniqueness theorem `Brockian.Spectral.golden_unique_to_five` is the
special case where `5 ∣ p` forces `p = 5`. -/
theorem golden_in_cycleSpectrum_iff_five_dvd {n : ℕ} (hn : 0 < n) :
    (Real.goldenRatio - 1) ∈ Brockian.Spectral.cycleSpectrum n ↔ 5 ∣ n := by
  constructor
  · -- Forward: the analytic pentagon argument, concluding `5 ∣ n`.
    rintro ⟨k, hk⟩
    -- hk : Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi * ↑k / ↑n)
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have h2pi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    -- reduce to a cosine equality
    have hcos : Real.cos (2 * Real.pi / 5)
        = Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) := by
      have h2 : (2 : ℝ) * Real.cos (2 * Real.pi / 5)
          = 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) := by
        rw [← Brockian.Spectral.golden_sub_one_eq_two_cos]; exact hk
      linarith
    rw [Real.cos_eq_cos_iff] at hcos
    obtain ⟨m, hm | hm⟩ := hcos
    · -- 2πk/n = 2mπ + 2π/5
      rw [div_eq_iff hnR] at hm
      have hstep : 2 * Real.pi * (k : ℝ)
          = 2 * Real.pi * (((m : ℝ) + 1 / 5) * (n : ℝ)) := by
        linear_combination hm
      have hk2 : (k : ℝ) = ((m : ℝ) + 1 / 5) * (n : ℝ) :=
        mul_left_cancel₀ h2pi hstep
      have hreal : (5 : ℝ) * (k : ℝ) = (n : ℝ) * (5 * (m : ℝ) + 1) := by
        linear_combination 5 * hk2
      have hz : (5 : ℤ) * (k : ℤ) = (n : ℤ) * (5 * m + 1) := by exact_mod_cast hreal
      have hdvd : (5 : ℤ) ∣ (n : ℤ) := ⟨(k : ℤ) - (n : ℤ) * m, by linear_combination -hz⟩
      exact_mod_cast hdvd
    · -- 2πk/n = 2mπ - 2π/5
      rw [div_eq_iff hnR] at hm
      have hstep : 2 * Real.pi * (k : ℝ)
          = 2 * Real.pi * (((m : ℝ) - 1 / 5) * (n : ℝ)) := by
        linear_combination hm
      have hk2 : (k : ℝ) = ((m : ℝ) - 1 / 5) * (n : ℝ) :=
        mul_left_cancel₀ h2pi hstep
      have hreal : (5 : ℝ) * (k : ℝ) = (n : ℝ) * (5 * (m : ℝ) - 1) := by
        linear_combination 5 * hk2
      have hz : (5 : ℤ) * (k : ℤ) = (n : ℤ) * (5 * m - 1) := by exact_mod_cast hreal
      have hdvd : (5 : ℤ) ∣ (n : ℤ) := ⟨(n : ℤ) * m - (k : ℤ), by linear_combination hz⟩
      exact_mod_cast hdvd
  · -- Backward: `n = 5j` ⇒ the k = j mode realizes `φ − 1`.
    rintro ⟨j, rfl⟩
    have hj0 : 0 < j := by omega
    refine ⟨j, ?_⟩
    have hj : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
    have harg : 2 * Real.pi * (j : ℝ) / ((5 * j : ℕ) : ℝ) = 2 * Real.pi / 5 := by
      push_cast
      field_simp
    rw [harg]
    exact (Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one).symm

/-- **Consistency: the prime case recovers `Brockian.Spectral.golden_unique_to_five`.**
For a prime `p`, `φ − 1 ∈ spec(C_p) ↔ p = 5`, since a prime divisible by 5 equals 5. -/
theorem golden_unique_to_five_recovered {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1) ∈ Brockian.Spectral.cycleSpectrum p ↔ p = 5 := by
  rw [golden_in_cycleSpectrum_iff_five_dvd hp.pos]
  constructor
  · intro h5p
    exact ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5p).symm
  · rintro rfl; norm_num

end Brockian.GoldenDivisibility
