/-
  Brockian/PentagonGrandEquivalence.lean — the master "Why Five" theorem.

  **The Grand Pentagon Equivalence.** For a prime `p`, four *independent*
  characterizations of the pentagon collapse to a single fact — `p = 5`:

    (0) `p = 5`                                                     [arithmetic];
    (1) `φ − 1` is an adjacency eigenvalue of the cycle `C_p`       [spectral];
    (2) the real cyclotomic field `ℚ(2cos 2π/p)` is quadratic       [Galois];
    (3) the fundamental mode `2cos(2π/p)` equals `φ − 1`            [trigonometric].

  We assemble the equivalence as a `List.TFAE`, routing every arrow through the
  three already-verified faces of the Brockian Pentagonal Law:

    * `Brockian.Spectral.golden_unique_to_five`      — (1) ↔ (0)  [spectral];
    * `Brockian.GaloisWhyFive.degree_five`           — (0) →  (2)  [Galois, p=5];
    * `Brockian.GaloisGeneralDegree.real_subfield_degree`
                                                     — (2) →  (0)  [Galois, general];
    * `Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one`
                                                     — (0) →  (3)  [trig];
    * `Brockian.CycleSpectrumFamily.mem_cycleSpectrum`
                                                     — (3) →  (1)  [spectral witness].

  The hub of the proof is `p = 5`: the cycle
      (1)→(4)→(2)→(1)   and   (1)→(3)→(1)
  is strongly connected, so `tfae_finish` derives all pairwise equivalences.
  The single delicate point is the prime `p = 2`, where `2cos(2π/2) = −2` is
  rational: there the Galois degree is `1 ≠ 2`, which the `(2)→(0)` arrow
  dispatches by contradiction.

  Verification:  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.Spectral
import Brockian.GaloisWhyFive
import Brockian.GaloisGeneralDegree
import Brockian.CycleSpectrumFamily

namespace Brockian.PentagonGrandEquivalence

open Brockian

/-- **The Grand Pentagon Equivalence.** For a prime `p`, the following are equivalent:
 (0) `p = 5`;
 (1) the golden value `φ − 1` is an adjacency eigenvalue of the cycle `C_p` [spectral];
 (2) the `p`-th real cyclotomic field `ℚ(2cos 2π/p)` is quadratic over `ℚ` [Galois];
 (3) the fundamental mode `2cos(2π/p)` equals `φ − 1` [trigonometric]. -/
theorem pentagon_grand_equivalence {p : ℕ} (hp : p.Prime) :
    List.TFAE
      [ p = 5,
        (Real.goldenRatio - 1) ∈ Brockian.Spectral.cycleSpectrum p,
        (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)).natDegree = 2,
        2 * Real.cos (2 * Real.pi / (p : ℝ)) = Real.goldenRatio - 1 ] := by
  -- (1) p = 5  →  (4) 2cos(2π/p) = φ − 1   [trigonometric identity at the pentagon]
  tfae_have 1 → 4 := by
    rintro rfl
    have hcast : ((5 : ℕ) : ℝ) = 5 := by norm_num
    rw [hcast]
    exact Brockian.CycleSpectrumFamily.two_cos_two_pi_div_five_eq_golden_sub_one
  -- (4) 2cos(2π/p) = φ − 1  →  (2) φ − 1 ∈ spec(C_p)   [k = 1 eigenvalue witness]
  tfae_have 4 → 2 := by
    intro h4
    have hmem := Brockian.CycleSpectrumFamily.mem_cycleSpectrum p 1
    rw [show 2 * Real.pi * ((1 : ℕ) : ℝ) / (p : ℝ) = 2 * Real.pi / (p : ℝ) by
          push_cast; ring] at hmem
    rwa [h4] at hmem
  -- (2) φ − 1 ∈ spec(C_p)  →  (1) p = 5   [spectral uniqueness]
  tfae_have 2 → 1 := (Brockian.Spectral.golden_unique_to_five hp).mp
  -- (1) p = 5  →  (3) [ℚ(α_p):ℚ] = 2   [the golden quadratic field]
  tfae_have 1 → 3 := by
    rintro rfl
    exact Brockian.GaloisWhyFive.degree_five
  -- (3) [ℚ(α_p):ℚ] = 2  →  (1) p = 5   [general degree = (p−1)/2, with p = 2 excluded]
  tfae_have 3 → 1 := by
    intro h3
    rcases eq_or_ne p 2 with rfl | hp2
    · -- p = 2 : α_2 = 2cos(π) = −2 is rational, so the degree is 1, contradicting 2.
      exfalso
      have hsg : Brockian.GaloisWhyFive.spectralGen 2 = -2 := by
        simp only [Brockian.GaloisWhyFive.spectralGen]
        rw [show (2 * Real.pi / ((2 : ℕ) : ℝ)) = Real.pi by push_cast; ring, Real.cos_pi]
        ring
      have hd1 : (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen 2)).natDegree = 1 := by
        rw [hsg, minpoly.natDegree_eq_one_iff, RingHom.mem_range]
        exact ⟨-2, by rw [map_neg]; norm_num⟩
      rw [hd1] at h3
      exact absurd h3 (by norm_num)
    · -- p ≠ 2 : natDegree = (p−1)/2 = 2 forces p ∈ {5, 6}; primality kills 6.
      have hpd : (p - 1) / 2 = 2 :=
        (Brockian.GaloisGeneralDegree.real_subfield_degree hp hp2).symm.trans h3
      have hle : 2 ≤ p := hp.two_le
      have hcases : p = 5 ∨ p = 6 := by omega
      rcases hcases with h5 | h6
      · exact h5
      · exfalso; rw [h6] at hp; exact absurd hp (by decide)
  tfae_finish

end Brockian.PentagonGrandEquivalence
