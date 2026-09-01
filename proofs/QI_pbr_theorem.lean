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

/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the Pusey–Barrett–Rudolph (PBR) theorem: in any ontological
(hidden-variable) model reproducing the quantum predictions, under the
*preparation independence* assumption, the probability distributions over ontic
states associated with two distinct (non-orthogonal) quantum preparations cannot
overlap.  Equivalently, the quantum state is *ontic* rather than *epistemic*.

Two ingredients are given.

* `QI.pbr_orthogonality` : the quantum input.  The four (unnormalised) PBR
  measurement vectors on `ℂ² ⊗ ℂ²` are pairwise orthogonal and each of them is
  orthogonal to exactly one of the four product preparations `|0⟩|0⟩`,
  `|0⟩|+⟩`, `|+⟩|0⟩`, `|+⟩|+⟩`.  Hence a quantum model predicts probability `0`
  for outcome `(i,j)` on preparation `(i,j)`.

* `QI.pbr_theorem` : the ontological conclusion.  Given an ontological model
  with response functions summing to one, preparation independence (the ontic
  state of two independently prepared systems is distributed according to the
  product measure) and the above zero predictions, any common component `q • ν`
  of the two preparation distributions must be trivial, i.e. `q = 0`.
-/

namespace QI

open MeasureTheory
open scoped ENNReal

/-! ## The quantum input: the PBR measurement -/

/-- Hermitian inner product on `ℂ⁴ = ℂ² ⊗ ℂ²`, whose index set is `Fin 2 × Fin 2`. -/
def cinner (u v : Fin 2 × Fin 2 → ℂ) : ℂ := ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (u p) * v p

/-- The two (unnormalised) one-qubit preparations: `|0⟩ = (1,0)` and `|+⟩ = (1,1)`. -/
def qubit : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![1, 1]]

/-- The product preparation `|ψ i⟩ ⊗ |ψ j⟩`. -/
def prep (i j : Fin 2) : Fin 2 × Fin 2 → ℂ := fun p => qubit i p.1 * qubit j p.2

/-- The four (unnormalised) PBR measurement vectors, indexed by `Fin 2 × Fin 2`:
`|0⟩|1⟩+|1⟩|0⟩`, `|0⟩|−⟩+|1⟩|+⟩`, `|+⟩|1⟩+|−⟩|0⟩`, `|+⟩|−⟩+|−⟩|+⟩`
(each rescaled by `√2`, resp. `2`, which does not affect orthogonality). -/
def pbrVec (i j : Fin 2) : Fin 2 × Fin 2 → ℂ := fun p =>
  (![![![![0, 1], ![1, 0]], ![![1, -1], ![1, 1]]],
     ![![![1, 1], ![-1, 1]], ![![2, 0], ![0, -2]]]] : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
    i j p.1 p.2

/-- The PBR measurement vectors are pairwise orthogonal, hence (after
normalisation) form an orthonormal basis of `ℂ² ⊗ ℂ²`, i.e. a genuine
projective measurement; and each is nonzero. -/
theorem pbrVec_orthogonal_basis :
    (∀ i j k l : Fin 2, (i, j) ≠ (k, l) → cinner (pbrVec i j) (pbrVec k l) = 0) ∧
      (∀ i j : Fin 2, cinner (pbrVec i j) (pbrVec i j) ≠ 0) := by
  constructor
  · decide +kernel
  · decide +kernel

/-- **Quantum input to PBR.**  The measurement outcome `(i,j)` has zero Born
probability on the product preparation `|ψ i⟩ ⊗ |ψ j⟩`. -/
theorem pbr_orthogonality (i j : Fin 2) : cinner (pbrVec i j) (prep i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cinner, pbrVec, prep, qubit, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-! ## The ontological conclusion -/

/-- **Pusey–Barrett–Rudolph theorem.**

Setting.  `Λ` is the space of ontic states.  Two quantum preparations `i : Fin 2`
(think of `|0⟩` and `|+⟩`) give rise to probability distributions `μ i` on `Λ`.
The four-outcome measurement of `pbrVec` performed on two independently prepared
systems is described by response functions `ξ k : Λ × Λ → ℝ≥0∞`, `k : Fin 2 × Fin 2`,
which sum to `1` at every ontic state (`hnorm`).  *Preparation independence*: the
joint ontic state of the two systems is distributed as the product measure
`(μ i).prod (μ j)`.  By `pbr_orthogonality` the quantum prediction for outcome
`(i,j)` on preparation `(i,j)` is `0`, which is hypothesis `hborn`.

Conclusion (the "ψ-ontic" statement, in contrapositive form).  If `ν` is a
probability measure and `q : ℝ≥0` is such that `q • ν` is a common component of
both preparation distributions (`hoverlap`) — i.e. the model is `ψ`-epistemic
with overlap at least `q` — then `q = 0`: distinct quantum states share no
common ontic component. -/
theorem pbr_theorem {Λ : Type*} [MeasurableSpace Λ]
    (μ : Fin 2 → Measure Λ) [∀ i, IsProbabilityMeasure (μ i)]
    (ξ : Fin 2 × Fin 2 → Λ × Λ → ℝ≥0∞) (hmeas : ∀ k, Measurable (ξ k))
    (hnorm : ∀ x, ∑ k : Fin 2 × Fin 2, ξ k x = 1)
    (hborn : ∀ i j : Fin 2, ∫⁻ x, ξ (i, j) x ∂((μ i).prod (μ j)) = 0)
    (ν : Measure Λ) [IsProbabilityMeasure ν] (q : ℝ≥0)
    (hoverlap : ∀ i : Fin 2, (q : ℝ≥0∞) • ν ≤ μ i) : q = 0 := by
  by_contra hq
  have hq0 : ((q : ℝ≥0∞)) ≠ 0 := by simpa using hq
  -- Each outcome has zero probability on the "overlap" product preparation.
  have key : ∀ k : Fin 2 × Fin 2, ∫⁻ x, ∫⁻ y, ξ k (x, y) ∂ν ∂ν = 0 := by
    rintro ⟨i, j⟩
    have h1 : ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂(μ j) ∂(μ i) = 0 := by
      rw [← lintegral_prod _ (hmeas (i, j)).aemeasurable]
      exact hborn i j
    have h2 : ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂((q : ℝ≥0∞) • ν) ∂((q : ℝ≥0∞) • ν)
        ≤ ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂(μ j) ∂(μ i) :=
      lintegral_mono' (hoverlap i) (fun _ => lintegral_mono' (hoverlap j) le_rfl)
    rw [h1, lintegral_smul_measure] at h2
    simp only [lintegral_smul_measure] at h2
    have h3 : (q : ℝ≥0∞) * ((q : ℝ≥0∞) * ∫⁻ x, ∫⁻ y, ξ (i, j) (x, y) ∂ν ∂ν) = 0 :=
      le_antisymm h2 (zero_le _)
    simpa [hq0] using h3
  -- But the response functions sum to one, so the total is one.
  have hone : ∫⁻ x, ∫⁻ y, (∑ k : Fin 2 × Fin 2, ξ k (x, y)) ∂ν ∂ν = 1 := by
    simp [hnorm]
  rw [show (fun x : Λ => ∫⁻ y, (∑ k : Fin 2 × Fin 2, ξ k (x, y)) ∂ν)
        = fun x : Λ => ∑ k : Fin 2 × Fin 2, ∫⁻ y, ξ k (x, y) ∂ν from
      funext fun x => lintegral_finset_sum _ (fun k _ => (hmeas k).comp measurable_prodMk_left),
    lintegral_finset_sum _
      (fun k _ => (hmeas k).lintegral_prod_right' (μ := ν))] at hone
  simp [key] at hone

end QI

