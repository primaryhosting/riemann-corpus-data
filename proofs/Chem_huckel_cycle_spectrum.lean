import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def cycleRoot (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The `k`-th Hückel π-energy level of the cycle `C n`, in units of the resonance
integral `β` (measured from the Coulomb integral `α`): `2 cos (2 π k / n)`. -/
noncomputable def huckelEnergy (n k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / n)

/-- The Vandermonde (discrete Fourier) matrix whose columns are the eigenvectors of the cycle. -/
noncomputable def cycleDFT (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vandermonde (fun j : Fin n => cycleRoot n ^ (j : ℕ))

lemma cycleDFT_apply (n : ℕ) (i k : Fin n) :
    cycleDFT n i k = cycleRoot n ^ ((i : ℕ) * (k : ℕ)) := by
  simp [cycleDFT, Matrix.vandermonde, pow_mul]

lemma cycleRoot_ne_zero (n : ℕ) : cycleRoot n ≠ 0 := Complex.exp_ne_zero _

lemma cycleRoot_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (cycleRoot n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma cycleRoot_pow_card {n : ℕ} (hn : n ≠ 0) : cycleRoot n ^ n = 1 :=
  (cycleRoot_isPrimitiveRoot hn).pow_eq_one

lemma cycleRoot_pow_congr {n a b : ℕ} (hn : n ≠ 0) (h : a % n = b % n) :
    cycleRoot n ^ a = cycleRoot n ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  conv_rhs => rw [← Nat.div_add_mod b n]
  rw [pow_add, pow_add, pow_mul, pow_mul, cycleRoot_pow_card hn, one_pow, one_pow, h]

/-- Stepping one vertex along the cycle multiplies the `k`-th eigenvector entry by `ω ^ k`. -/
lemma cycleRoot_step {m : ℕ} (j k : Fin (m + 3)) :
    cycleRoot (m + 3) ^ (((j + 1 : Fin (m + 3)) : ℕ) * (k : ℕ))
      = cycleRoot (m + 3) ^ ((j : ℕ) * (k : ℕ)) * cycleRoot (m + 3) ^ ((k : ℕ)) := by
  rw [← pow_add]
  refine cycleRoot_pow_congr (by omega) ?_
  have h1 : ((j + 1 : Fin (m + 3)) : ℕ) = ((j : ℕ) + 1) % (m + 3) := by
    rw [Fin.val_add]
    congr 1
  have h2 : ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) := by ring
  rw [h1, ← h2]
  exact (Nat.mod_modEq _ _).mul_right _

lemma huckelEnergy_eq {n k : ℕ} (hn : n ≠ 0) :
    ((huckelEnergy n k : ℝ) : ℂ) = cycleRoot n ^ k + (cycleRoot n ^ k)⁻¹ := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow : cycleRoot n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
    rw [cycleRoot, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [hpow, huckelEnergy, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma sub_one_ne_add_one {m : ℕ} (i : Fin (m + 3)) : (i - 1 : Fin (m + 3)) ≠ i + 1 := by
  intro h
  have h2 : (2 : Fin (m + 3)) = 0 := by
    have hz : (i + 1) - (i - 1) = (0 : Fin (m + 3)) := by rw [h, sub_self]
    rw [← hz, show (2 : Fin (m + 3)) = 1 + 1 from rfl]
    abel
  have h3 := congrArg Fin.val h2
  rw [show ((2 : Fin (m + 3)) : ℕ) = 2 % (m + 3) from rfl, Nat.mod_eq_of_lt (by omega)] at h3
  simp at h3

/-- The eigen-equation for the cycle: `A * F = F * D`, where `F` is the Fourier matrix and
`D` is the diagonal matrix of Hückel energies. -/
lemma adjMatrix_mul_cycleDFT (m : ℕ) :
    (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ * cycleDFT (m + 3)
      = cycleDFT (m + 3) *
        Matrix.diagonal (fun k : Fin (m + 3) => ((huckelEnergy (m + 3) k : ℝ) : ℂ)) := by
  ext i k
  have hstep : ∀ j : Fin (m + 3),
      cycleDFT (m + 3) (j + 1) k = cycleDFT (m + 3) j k * cycleRoot (m + 3) ^ ((k : ℕ)) := by
    intro j
    rw [cycleDFT_apply, cycleDFT_apply]
    exact cycleRoot_step j k
  have hLHS : ((SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ * cycleDFT (m + 3)) i k
      = ((SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ *ᵥ (fun j => cycleDFT (m + 3) j k)) i := rfl
  rw [hLHS, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i), Matrix.mul_diagonal,
    huckelEnergy_eq (n := m + 3) (by omega), hstep i]
  have h1 : cycleDFT (m + 3) i k
      = cycleDFT (m + 3) (i - 1) k * cycleRoot (m + 3) ^ ((k : ℕ)) := by
    have h := hstep (i - 1)
    rwa [sub_add_cancel] at h
  have hz : cycleRoot (m + 3) ^ ((k : ℕ)) ≠ 0 := pow_ne_zero _ (cycleRoot_ne_zero _)
  rw [h1]
  field_simp
  ring

lemma cycleDFT_isUnit (m : ℕ) : IsUnit (cycleDFT (m + 3)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [cycleDFT, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  have hval : (j : ℕ) = (i : ℕ) :=
    (cycleRoot_isPrimitiveRoot (n := m + 3) (by omega)).pow_inj j.isLt i.isLt h
  exact hj.ne' (Fin.ext hval)

/-- The characteristic polynomial of the Hückel (adjacency) matrix of the cycle `C n`,
for `n ≥ 3`, is `∏ k, (X - 2 cos (2 π k / n))`. -/
theorem huckel_cycle_charpoly {n : ℕ} (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ).charpoly
      = ∏ k : Fin n, (X - C ((huckelEnergy n k : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨u, hu⟩ := cycleDFT_isUnit m
  have hkey := adjMatrix_mul_cycleDFT m
  rw [← hu] at hkey
  have hA : (SimpleGraph.cycleGraph (m + 3)).adjMatrix ℂ
      = (u : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) *
          Matrix.diagonal (fun k : Fin (m + 3) => ((huckelEnergy (m + 3) k : ℝ) : ℂ)) *
          (↑u⁻¹ : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) := by
    rw [← hkey, mul_assoc, Units.mul_inv, mul_one]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel spectrum of the cycle.** The eigenvalues of the adjacency (Hückel) matrix of the
cycle graph `C n` for `n ≥ 3` are exactly the π-energies `2 cos (2 π k / n)`,
`k = 0, …, n - 1`. -/
theorem huckel_cycle_spectrum {n : ℕ} (hn : 3 ≤ n) :
    spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = {μ : ℂ | ∃ k < n, μ = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)} := by
  ext μ
  rw [Set.mem_setOf_eq, Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_cycle_charpoly hn]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, k.isLt, by rw [sub_eq_zero] at hk; exact hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, by simp [huckelEnergy]⟩

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

