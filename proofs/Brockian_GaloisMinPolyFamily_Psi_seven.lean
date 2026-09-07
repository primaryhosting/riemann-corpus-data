/-
  Brockian/GaloisMinPolyFamily.lean — the EXPLICIT minimal polynomial family
  of the spectral generator `2 cos(2π/p)`.

  `Brockian/GaloisWhyFive.lean` exhibits the concrete annihilators
  `Q5 = X²+X−1` and `P7 = X³+X²−2X−1` for the primes `p = 5, 7`, and
  `Brockian/GaloisGeneralDegree.lean` proves the GENERAL degree
  `(minpoly ℚ (2cos 2π/p)).natDegree = (p−1)/2` for every odd prime.  What was
  still missing is the minimal polynomial itself, *as a family*.  This file
  supplies it.

  ## The family

  Write `α_p = 2 cos(2π/p) = ζ_p + ζ_p⁻¹`.  Let `Cₖ = Chebyshev.C ℚ k` be
  Mathlib's rescaled Chebyshev polynomial of the first kind, the unique monic
  integer polynomial with `Cₖ(2 cos θ) = 2 cos(kθ)` (`C_two_mul_real_cos`).
  Define, with `m = (p−1)/2`,

        Ψ_p  :=  1  +  ∑_{k=1}^{m} Cₖ .

  Since `Cₖ` is monic of degree `k`, the sum is monic of degree `m = (p−1)/2`.
  Evaluating at `α_p`:

        Ψ_p(α_p) = 1 + ∑_{k=1}^{m} 2 cos(2πk/p)
                 = ∑_{j=0}^{p−1} cos(2πj/p)          (folding k ↔ p−k)
                 = Re ∑_{j=0}^{p−1} ζ_p^j  =  Re 0  =  0,

  the sum of all `p`-th roots of unity.  Combined with the general degree
  theorem, `Ψ_p = minpoly ℚ (2cos 2π/p)`.  The concrete cases reproduce
  `Ψ_5 = X²+X−1 = Q5` and `Ψ_7 = X³+X²−2X−1 = P7`.

  ## What is proved (AXLE-verified @ lean-4.32.0, axioms ⊆
     {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`)

    * `Psi p`                    — the family `1 + ∑_{k=1}^{(p−1)/2} Cₖ`.
    * `Psi_monic`                — **level 1**: `Ψ_p` is monic (odd primes).
    * `Psi_natDegree`            — **level 1**: `(Ψ_p).natDegree = (p−1)/2`.
    * `aeval_spectralGen_Psi`    — **level 2**: `Ψ_p(2cos 2π/p) = 0` — the
                                   contact with the transcendental generator,
                                   via the geometric sum of `p`-th roots of unity.
    * `Psi_eq_minpoly`           — **level 3**: `Ψ_p = minpoly ℚ (2cos 2π/p)`
                                   for every odd prime `p` (annihilation +
                                   monic + the general degree of
                                   `GaloisGeneralDegree`).
    * `Psi_five`, `Psi_seven`    — sanity: `Ψ_5 = Q5`, `Ψ_7 = P7`.
    * `minpoly_five`,
      `minpoly_seven`            — `minpoly ℚ (2cos 2π/5) = X²+X−1`,
                                   `minpoly ℚ (2cos 2π/7) = X³+X²−2X−1`.
    * `C_facts`, `psiAux`        — the monicity/degree engine for `Chebyshev.C`
                                   over `ℚ` (no such lemma is in Mathlib 4.32).

  ## What is NOT proved

    * `p = 2` is excluded (there `2cos(π) = −2 ∈ ℚ`, degree 1, the degenerate
      boundary case); the same exclusion as `GaloisGeneralDegree`.  For all odd
      primes the identification `Ψ_p = minpoly` is complete.

  ## Precise remaining obstruction

    * None for the stated target.  Every ingredient is closed here or imported:
      the family and its monic/degree/annihilation facts are proved from
      Mathlib's `Polynomial.Chebyshev.C_two_mul_real_cos`,
      `IsPrimitiveRoot.geom_sum_eq_zero`, and `Complex.isPrimitiveRoot_exp`;
      the degree equality rests on `GaloisGeneralDegree.real_subfield_degree`.
-/
import Mathlib
import Brockian.Spectral
import Brockian.GaloisWhyFive
import Brockian.GaloisGeneralDegree

namespace Brockian.GaloisMinPolyFamily

open Polynomial

/-! ### Monicity and degree of the rescaled Chebyshev polynomials `Cₖ`

Mathlib provides `Chebyshev.C R n` with `C 0 = 2`, `C 1 = X`,
`C (n+2) = X·C (n+1) − C n`, but no monic/degree lemma.  We supply them by a
single ordinary induction carrying `Cₙ₊₁` (monic, degree `n+1`) together with a
degree bound on `Cₙ`. -/

/-- The three simultaneous facts making `Cₖ` monic of degree `k`:
`C ℚ (n+1)` is monic of degree `n+1`, and `C ℚ n` has degree `≤ n`. -/
lemma C_facts : ∀ n : ℕ,
    (Chebyshev.C ℚ ((n + 1 : ℕ) : ℤ)).Monic ∧
    (Chebyshev.C ℚ ((n + 1 : ℕ) : ℤ)).natDegree = n + 1 ∧
    (Chebyshev.C ℚ (n : ℤ)).natDegree ≤ n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num, Chebyshev.C_one]; exact monic_X
    · rw [show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num, Chebyshev.C_one]; exact natDegree_X
    · rw [show ((0 : ℕ) : ℤ) = 0 from by norm_num, Chebyshev.C_zero]; simp
  | succ n ih =>
    obtain ⟨ihm, ihd, ihle⟩ := ih
    have e3 : (((n + 1) + 1 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hCm1 : (Chebyshev.C ℚ ((n : ℤ) + 1)).Monic := by rw [← e2]; exact ihm
    have hCd1 : (Chebyshev.C ℚ ((n : ℤ) + 1)).natDegree = n + 1 := by rw [← e2]; exact ihd
    have hrec : Chebyshev.C ℚ ((n : ℤ) + 2)
        = X * Chebyshev.C ℚ ((n : ℤ) + 1) - Chebyshev.C ℚ (n : ℤ) := Chebyshev.C_add_two ℚ (n : ℤ)
    have hXA_monic : (X * Chebyshev.C ℚ ((n : ℤ) + 1)).Monic := monic_X.mul hCm1
    have hXA_deg : (X * Chebyshev.C ℚ ((n : ℤ) + 1)).natDegree = n + 2 := by
      have h := monic_X.natDegree_mul hCm1
      rw [Polynomial.natDegree_X, hCd1] at h
      omega
    have hBlt : (Chebyshev.C ℚ (n : ℤ)).natDegree
        < (X * Chebyshev.C ℚ ((n : ℤ) + 1)).natDegree := by rw [hXA_deg]; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [e3, hrec, sub_eq_add_neg]
      exact hXA_monic.add_of_left
        (by rw [Polynomial.degree_neg]; exact Polynomial.degree_lt_degree hBlt)
    · have hd : (Chebyshev.C ℚ ((n : ℤ) + 2)).natDegree = n + 1 + 1 := by
        rw [hrec, sub_eq_add_neg,
          Polynomial.natDegree_add_eq_left_of_natDegree_lt
            (by rw [Polynomial.natDegree_neg]; exact hBlt)]
        omega
      rw [e3, hd]
    · exact ihd.le

/-- The monic/degree engine for the family: for every `M`, the partial sum
`1 + ∑_{k=0}^{M} C ℚ (k+1)` is monic of degree `M+1`. -/
lemma psiAux : ∀ M : ℕ,
    ((1 : ℚ[X]) + ∑ k ∈ Finset.range (M + 1), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ)).Monic ∧
    ((1 : ℚ[X]) + ∑ k ∈ Finset.range (M + 1), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ)).natDegree = M + 1 := by
  intro M
  induction M with
  | zero =>
    have hkey : (1 : ℚ[X]) + ∑ k ∈ Finset.range (0 + 1), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ) = X + 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num, Chebyshev.C_one]
      ring
    rw [hkey]
    refine ⟨monic_X.add_of_left (Polynomial.degree_lt_degree (by simp)), ?_⟩
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp), Polynomial.natDegree_X]
  | succ M ih =>
    obtain ⟨_, ihd⟩ := ih
    have hCm := (C_facts (M + 1)).1
    have hCd := (C_facts (M + 1)).2.1
    have hkey : (1 : ℚ[X]) + ∑ k ∈ Finset.range (M + 1 + 1), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ)
        = Chebyshev.C ℚ ((M + 1 + 1 : ℕ) : ℤ)
          + (1 + ∑ k ∈ Finset.range (M + 1), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ)) := by
      rw [Finset.sum_range_succ]; ring
    rw [hkey]
    have hlt : ((1 : ℚ[X]) + ∑ k ∈ Finset.range (M + 1), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ)).natDegree
        < (Chebyshev.C ℚ ((M + 1 + 1 : ℕ) : ℤ)).natDegree := by rw [ihd, hCd]; omega
    refine ⟨hCm.add_of_left (Polynomial.degree_lt_degree hlt), ?_⟩
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hCd]

/-! ### The family -/

/-- **`Ψ_p = 1 + ∑_{k=1}^{(p−1)/2} Cₖ`** — the explicit monic integer family whose
value at `2 cos(2π/p)` vanishes.  Here `Cₖ = Chebyshev.C ℚ k` satisfies
`Cₖ(2 cos θ) = 2 cos(kθ)`. -/
noncomputable def Psi (p : ℕ) : ℚ[X] :=
  1 + ∑ k ∈ Finset.range ((p - 1) / 2), Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ)

/-- **Level 1 (monicity).**  For every odd prime `p`, `Ψ_p` is monic. -/
theorem Psi_monic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (Psi p).Monic := by
  have h2 := hp.two_le
  obtain ⟨M, hM⟩ : ∃ M, (p - 1) / 2 = M + 1 := ⟨(p - 1) / 2 - 1, by omega⟩
  unfold Psi
  rw [hM]
  exact (psiAux M).1

/-- **Level 1 (degree).**  For every odd prime `p`, `(Ψ_p).natDegree = (p−1)/2`. -/
theorem Psi_natDegree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (Psi p).natDegree = (p - 1) / 2 := by
  have h2 := hp.two_le
  obtain ⟨M, hM⟩ : ∃ M, (p - 1) / 2 = M + 1 := ⟨(p - 1) / 2 - 1, by omega⟩
  unfold Psi
  rw [hM, (psiAux M).2]

/-! ### Level 2: annihilation of the transcendental generator -/

/-- **Level 2.**  The family annihilates the spectral generator:
`Ψ_p(2 cos 2π/p) = 0` for every odd prime `p`.  The key contact with the
transcendental generator, proved by folding the cosine sum into the real part of
the geometric sum `∑_{j<p} ζ_p^j = 0`. -/
theorem aeval_spectralGen_Psi {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    aeval (Brockian.GaloisWhyFive.spectralGen p) (Psi p) = 0 := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  have h2 := hp.two_le
  set θ : ℝ := 2 * Real.pi / (p : ℝ) with hθ
  have hspec : Brockian.GaloisWhyFive.spectralGen p = 2 * Real.cos θ := by rw [hθ]; rfl
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  obtain ⟨m, hp2m⟩ : ∃ m, p = 2 * m + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2; exact ⟨k, hk⟩
  have hmval : (p - 1) / 2 = m := by omega
  have hpR : (p : ℝ) = 2 * (m : ℝ) + 1 := by rw [hp2m]; push_cast; ring
  have hpθ : (2 * (m : ℝ) + 1) * θ = 2 * Real.pi := by
    rw [hθ, ← hpR, ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hpne
  -- (B) the geometric sum of all p-th roots of unity has zero real part
  have hB0 : ∑ j ∈ Finset.range p, Real.cos ((j : ℝ) * θ) = 0 := by
    have hζ : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))) p :=
      Complex.isPrimitiveRoot_exp p hp0
    have hgeom := hζ.geom_sum_eq_zero (by omega : 1 < p)
    have hcongr : ∀ j ∈ Finset.range p,
        Real.cos ((j : ℝ) * θ)
          = ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))) ^ j).re := by
      intro j _
      rw [← Complex.exp_nat_mul,
        show (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))
          = (((j : ℝ) * θ : ℝ) : ℂ) * Complex.I from by rw [hθ]; push_cast; ring,
        Complex.exp_ofReal_mul_I_re]
    rw [Finset.sum_congr rfl hcongr, ← Complex.re_sum, hgeom, Complex.zero_re]
  -- (split) fold the p-th root sum into 1 + 2·(half sum)
  have hsplit : ∑ j ∈ Finset.range p, Real.cos ((j : ℝ) * θ)
      = 1 + 2 * ∑ k ∈ Finset.range m, Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
    rw [hp2m, Finset.sum_range_succ']
    have hf0 : Real.cos (((0 : ℕ) : ℝ) * θ) = 1 := by simp
    rw [hf0]
    have hcons : ∑ k ∈ Finset.range (2 * m), Real.cos (((k + 1 : ℕ) : ℝ) * θ)
        = (∑ k ∈ Finset.Ico 0 m, Real.cos (((k + 1 : ℕ) : ℝ) * θ))
          + (∑ k ∈ Finset.Ico m (2 * m), Real.cos (((k + 1 : ℕ) : ℝ) * θ)) := by
      rw [Finset.range_eq_Ico]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le m) (by omega)).symm
    have hlow : ∑ k ∈ Finset.Ico 0 m, Real.cos (((k + 1 : ℕ) : ℝ) * θ)
        = ∑ k ∈ Finset.range m, Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
      rw [Finset.range_eq_Ico]
    have hhigh : ∑ k ∈ Finset.Ico m (2 * m), Real.cos (((k + 1 : ℕ) : ℝ) * θ)
        = ∑ k ∈ Finset.range m, Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
      rw [Finset.sum_Ico_eq_sum_range, show 2 * m - m = m from by omega,
        ← Finset.sum_range_reflect (fun i => Real.cos ((((m + i) + 1 : ℕ) : ℝ) * θ)) m]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      show Real.cos ((((m + (m - 1 - i)) + 1 : ℕ) : ℝ) * θ) = Real.cos (((i + 1 : ℕ) : ℝ) * θ)
      rw [show m + (m - 1 - i) + 1 = 2 * m - i from by omega,
        show ((2 * m - i : ℕ) : ℝ) = 2 * (m : ℝ) - (i : ℝ) from by
          rw [Nat.cast_sub (by omega)]; push_cast; ring,
        show (2 * (m : ℝ) - (i : ℝ)) * θ = 2 * Real.pi - ((i : ℝ) + 1) * θ from by
          linear_combination hpθ,
        Real.cos_two_pi_sub]
      congr 1; push_cast; ring
    have hQ : ∑ k ∈ Finset.range (2 * m), Real.cos (((k + 1 : ℕ) : ℝ) * θ)
        = 2 * ∑ k ∈ Finset.range m, Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
      rw [hcons, hlow, hhigh]; ring
    rw [hQ]; ring
  -- reduce the aeval to the cosine sum and conclude
  unfold Psi
  rw [hmval, map_add, map_one, map_sum]
  have hterm : ∀ k ∈ Finset.range m,
      (aeval (Brockian.GaloisWhyFive.spectralGen p)) (Chebyshev.C ℚ ((k + 1 : ℕ) : ℤ))
        = 2 * Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
    intro k _
    rw [Chebyshev.aeval_C, hspec, Chebyshev.C_two_mul_real_cos]
    norm_cast
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hsplit]
  exact hB0

/-! ### Level 3: the family IS the minimal polynomial -/

/-- **Level 3.**  For every odd prime `p`, the family is exactly the minimal
polynomial of the spectral generator:
`Ψ_p = minpoly ℚ (2 cos 2π/p)`.  Monic annihilator of the right degree. -/
theorem Psi_eq_minpoly {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Psi p = minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p) := by
  have hmon := Psi_monic hp hp2
  have hann := aeval_spectralGen_Psi hp hp2
  have hint : IsIntegral ℚ (Brockian.GaloisWhyFive.spectralGen p) := ⟨Psi p, hmon, hann⟩
  have hdvd : minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p) ∣ Psi p :=
    minpoly.dvd ℚ _ hann
  have hmpmon : (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)).Monic := minpoly.monic hint
  have hdegeq : (Psi p).natDegree = (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)).natDegree := by
    rw [Psi_natDegree hp hp2, Brockian.GaloisGeneralDegree.real_subfield_degree hp hp2]
  have hassoc : Associated (minpoly ℚ (Brockian.GaloisWhyFive.spectralGen p)) (Psi p) :=
    associated_of_dvd_of_natDegree_le hdvd hmon.ne_zero (le_of_eq hdegeq)
  exact (eq_of_monic_of_associated hmpmon hmon hassoc).symm

/-! ### Sanity corollaries: `Ψ_5 = Q5`, `Ψ_7 = P7` -/

/-- `Ψ_5 = X²+X−1 = Q5`, matching `GaloisWhyFive`. -/
theorem Psi_five : Psi 5 = Brockian.GaloisWhyFive.Q5 := by
  unfold Psi Brockian.GaloisWhyFive.Q5
  rw [show (5 - 1) / 2 = 0 + 1 + 1 from by norm_num,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    show (((0 + 1) + 1 : ℕ) : ℤ) = 2 from by norm_num,
    show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num, Chebyshev.C_one, Chebyshev.C_two]
  ring

/-- `Ψ_7 = X³+X²−2X−1 = P7`, matching `GaloisWhyFive`. -/
theorem Psi_seven : Psi 7 = Brockian.GaloisWhyFive.P7 := by
  have hC3 : Chebyshev.C ℚ (3 : ℤ) = X ^ 3 - 3 * X := by
    have h := Chebyshev.C_add_two ℚ (1 : ℤ)
    rw [show (1 : ℤ) + 2 = 3 from by norm_num, show (1 : ℤ) + 1 = 2 from by norm_num,
      Chebyshev.C_two, Chebyshev.C_one] at h
    rw [h]; ring
  unfold Psi Brockian.GaloisWhyFive.P7
  rw [show (7 - 1) / 2 = 0 + 1 + 1 + 1 from by norm_num,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    show ((((0 + 1) + 1) + 1 : ℕ) : ℤ) = 3 from by norm_num,
    show (((0 + 1) + 1 : ℕ) : ℤ) = 2 from by norm_num,
    show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num,
    Chebyshev.C_one, Chebyshev.C_two, hC3]
  ring

/-- `minpoly ℚ (2 cos 2π/5) = X²+X−1`, from the family. -/
theorem minpoly_five :
    minpoly ℚ (Brockian.GaloisWhyFive.spectralGen 5) = Brockian.GaloisWhyFive.Q5 := by
  rw [← Psi_eq_minpoly (by norm_num) (by norm_num)]; exact Psi_five

/-- `minpoly ℚ (2 cos 2π/7) = X³+X²−2X−1`, from the family. -/
theorem minpoly_seven :
    minpoly ℚ (Brockian.GaloisWhyFive.spectralGen 7) = Brockian.GaloisWhyFive.P7 := by
  rw [← Psi_eq_minpoly (by norm_num) (by norm_num)]; exact Psi_seven

end Brockian.GaloisMinPolyFamily
