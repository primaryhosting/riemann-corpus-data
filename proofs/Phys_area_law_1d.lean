/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Phys

/-- The entanglement entropy of a bipartite pure state, expressed in terms of its Schmidt
spectrum `p` (the squared Schmidt coefficients across a cut, i.e. the eigenvalues of the
reduced density matrix): `S = -∑ᵢ pᵢ log pᵢ`.  Terms with `pᵢ = 0` contribute `0`, matching
the usual convention `0 log 0 = 0`. -/
noncomputable def entanglementEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, -(p i * Real.log (p i))

/-- The Schmidt rank of a spectrum: the number of nonzero Schmidt coefficients.  For a gapped
1D ground state this is (up to an approximation error) bounded by the bond dimension of an
MPS representation, uniformly in the size of the region. -/
noncomputable def schmidtRank {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℕ :=
  (Finset.univ.filter fun i => p i ≠ 0).card

/-- Elementary pointwise bound behind the entropy bound: for `q > 0` and `n ≥ 1`,
`-q log q - q log n ≤ 1/n - q`.  This is `log x ≤ x - 1` applied at `x = 1/(q n)`. -/
lemma term_bound {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 0 < q) :
    -(q * Real.log q) - q * Real.log n ≤ 1 / n - q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < 1 / (q * n) := by positivity
  have hlog : Real.log (1 / (q * n)) ≤ 1 / (q * n) - 1 :=
    Real.log_le_sub_one_of_pos hx
  have hrw : Real.log (1 / (q * n)) = -(Real.log q) - Real.log n := by
    rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hq) (ne_of_gt hnR)]
    ring
  have hmul : q * Real.log (1 / (q * n)) ≤ q * (1 / (q * n) - 1) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt hq)
  rw [hrw] at hmul
  have hq' : q * (1 / (q * n) - 1) = 1 / n - q := by
    field_simp
  calc -(q * Real.log q) - q * Real.log n = q * (-(Real.log q) - Real.log n) := by ring
    _ ≤ q * (1 / (q * n) - 1) := hmul
    _ = 1 / n - q := hq'

/-- **Key intermediate lemma.**  The entropy of a probability distribution is at most the
logarithm of the number of outcomes it is supported on:  `S(p) ≤ log (schmidtRank p)`. -/
theorem entropy_le_log_schmidtRank {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    entanglementEntropy p ≤ Real.log (schmidtRank p) := by
  classical
  set S : Finset ι := Finset.univ.filter fun i => p i ≠ 0 with hS
  set n : ℕ := S.card with hn
  -- the support is nonempty since the total mass is `1`
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : ∑ i, p i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      by_contra hi
      have : i ∈ S := by simp [hS, hi]
      simp [h] at this
    rw [hsum] at this
    norm_num at this
  have hn0 : 0 < n := Finset.card_pos.mpr hSne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  -- restrict the entropy sum to the support
  have hrestrict : entanglementEntropy p = ∑ i ∈ S, -(p i * Real.log (p i)) := by
    rw [entanglementEntropy]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    have : p i = 0 := by
      by_contra h
      exact hi (by simp [hS, h])
    simp [this]
  -- the mass on the support is still 1
  have hsumS : ∑ i ∈ S, p i = 1 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro i _ hi
    by_contra h
    exact hi (by simp [hS, h])
  have hkey : ∑ i ∈ S, (-(p i * Real.log (p i)) - p i * Real.log n) ≤ 0 := by
    have hb : ∀ i ∈ S, -(p i * Real.log (p i)) - p i * Real.log n ≤ 1 / (n : ℝ) - p i := by
      intro i hi
      have hpi : 0 < p i := by
        rcases lt_or_eq_of_le (hp i) with h | h
        · exact h
        · exact absurd h.symm (by simpa [hS] using hi)
      exact term_bound hn0 hpi
    calc ∑ i ∈ S, (-(p i * Real.log (p i)) - p i * Real.log n)
        ≤ ∑ i ∈ S, (1 / (n : ℝ) - p i) := Finset.sum_le_sum hb
      _ = 0 := by
          rw [Finset.sum_sub_distrib, hsumS, Finset.sum_const, hn.symm]
          field_simp
  have hexp : ∑ i ∈ S, (-(p i * Real.log (p i)) - p i * Real.log n)
      = (∑ i ∈ S, -(p i * Real.log (p i))) - Real.log n := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsumS, one_mul]
  rw [hexp] at hkey
  rw [hrestrict]
  linarith [hkey]

/-- **Area law for gapped 1D ground states (Hastings), in Schmidt-spectrum form.**

Consider a one-dimensional chain and a family of cuts, indexed by the size `L` of the region
`A = [1, L]`.  For each `L`, `p L` is the Schmidt spectrum of the ground state across that cut
(a probability distribution: the eigenvalues of the reduced density matrix `ρ_A`).

The hard analytic content of Hastings' theorem is that a nonvanishing spectral gap forces the
Schmidt rank across every cut to be bounded by a constant `D` (the bond dimension of an
efficient MPS approximation), *independent of the region size `L`*; that boundedness is taken
here as the hypothesis `hrank`.

The conclusion is the area law itself: there is a single constant `C`, independent of `L`,
bounding the entanglement entropy `S(A) = -tr ρ_A log ρ_A` of every region — the entropy does
not grow with the volume `L` of the region, but is governed by the (zero-dimensional) boundary
of the cut.  Explicitly one may take `C = log D`. -/
theorem area_law_1d {ι : Type*} [Fintype ι] (D : ℕ) (hD : 0 < D) (p : ℕ → ι → ℝ)
    (hp : ∀ L i, 0 ≤ p L i) (hsum : ∀ L, ∑ i, p L i = 1)
    (hrank : ∀ L, schmidtRank (p L) ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, entanglementEntropy (p L) ≤ C := by
  refine ⟨Real.log D, Real.log_nonneg (by exact_mod_cast hD), fun L => ?_⟩
  refine le_trans (entropy_le_log_schmidtRank (p L) (hp L) (hsum L)) ?_
  have h1 : (schmidtRank (p L) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hrank L
  rcases Nat.eq_zero_or_pos (schmidtRank (p L)) with h | h
  · simp [h, Real.log_nonneg (by exact_mod_cast hD : (1:ℝ) ≤ D)]
  · exact Real.log_le_log (by exact_mod_cast h) h1

end Phys

