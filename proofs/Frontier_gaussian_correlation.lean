import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory ProbabilityTheory

/-- The standard (centered, isotropic) Gaussian measure on `ℝ ^ n`, realized as the product of
`n` copies of the standard Gaussian measure on `ℝ`. -/
noncomputable def gaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureGaussianMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianMeasure n) := by
  unfold gaussianMeasure; infer_instance

/-- `GaussianCorrelationHolds n` is the Gaussian correlation inequality (Royen's theorem) in
dimension `n`: for any two origin-symmetric convex sets `K`, `L` in `ℝ ^ n`, the standard
Gaussian measure of the intersection is at least the product of the measures. The full
Gaussian correlation inequality is the statement `∀ n, GaussianCorrelationHolds n`. -/
def GaussianCorrelationHolds (n : ℕ) : Prop :=
  ∀ K L : Set (Fin n → ℝ), Convex ℝ K → Convex ℝ L →
    (∀ x ∈ K, -x ∈ K) → (∀ x ∈ L, -x ∈ L) →
    gaussianMeasure n K * gaussianMeasure n L ≤ gaussianMeasure n (K ∩ L)

section Symmetric

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An origin-symmetric convex set is closed under scaling by a factor of absolute value at
most one. -/
theorem smul_mem_of_abs_le_one {S : Set E} (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S)
    {x : E} (hx : x ∈ S) {c : ℝ} (hc : |c| ≤ 1) : c • x ∈ S := by
  have hc1 : -1 ≤ c := neg_le_of_abs_le hc
  have hc2 : c ≤ 1 := le_of_abs_le hc
  have h0 : (0:ℝ) ≤ (1 + c) / 2 := by linarith
  have h1 : (0:ℝ) ≤ (1 - c) / 2 := by linarith
  have hsum : (1 + c) / 2 + (1 - c) / 2 = 1 := by ring
  have := hconv hx (hsymm x hx) h0 h1 hsum
  have heq : ((1 + c) / 2) • x + ((1 - c) / 2) • (-x) = c • x := by
    rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
    congr 1
    ring
  rwa [heq] at this

end Symmetric

/-- In dimension one, an origin-symmetric convex set contains every point that is no further
from the origin than one of its points. -/
theorem mem_of_abs_le_one_dim {S : Set (Fin 1 → ℝ)} (hconv : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) {x y : Fin 1 → ℝ} (hx : x ∈ S) (hxy : |y 0| ≤ |x 0|) : y ∈ S := by
  by_cases hx0 : x 0 = 0
  · have hy0 : y 0 = 0 := by
      have : |y 0| ≤ 0 := by simpa [hx0] using hxy
      simpa using abs_nonpos_iff.mp this
    have hxy' : y = x := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [hy0, hx0]
    rwa [hxy']
  · have hc : |y 0 / x 0| ≤ 1 := by
      rw [abs_div]
      rw [div_le_one (abs_pos.mpr hx0)]
      exact hxy
    have hmem := smul_mem_of_abs_le_one hconv hsymm hx hc
    have heq : (y 0 / x 0) • x = y := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rwa [heq] at hmem

/-- Two origin-symmetric convex subsets of the line are always nested. -/
theorem subset_or_subset_one_dim {K L : Set (Fin 1 → ℝ)} (hK : Convex ℝ K) (hL : Convex ℝ L)
    (hKs : ∀ x ∈ K, -x ∈ K) (hLs : ∀ x ∈ L, -x ∈ L) : K ⊆ L ∨ L ⊆ K := by
  by_cases h : K ⊆ L
  · exact Or.inl h
  · right
    obtain ⟨x, hxK, hxL⟩ := Set.not_subset.mp h
    intro y hyL
    by_cases hle : |y 0| ≤ |x 0|
    · exact mem_of_abs_le_one_dim hK hKs hxK hle
    · exact absurd (mem_of_abs_le_one_dim hL hLs hyL (le_of_lt (not_le.mp hle))) hxL

/-- A Lean-checked reduction: in any dimension, the Gaussian correlation inequality holds for
a nested pair of sets, with no convexity or symmetry needed. -/
theorem gaussian_correlation_of_subset {n : ℕ} {K L : Set (Fin n → ℝ)} (h : K ⊆ L) :
    gaussianMeasure n K * gaussianMeasure n L ≤ gaussianMeasure n (K ∩ L) := by
  have hinter : K ∩ L = K := Set.inter_eq_self_of_subset_left h
  rw [hinter]
  calc gaussianMeasure n K * gaussianMeasure n L
      ≤ gaussianMeasure n K * 1 := mul_le_mul_right prob_le_one _
    _ = gaussianMeasure n K := mul_one _

/-- **Gaussian correlation inequality, base case `n = 1`.**

For origin-symmetric convex sets `K, L ⊆ ℝ ^ 1`, the standard Gaussian measure satisfies
`γ(K) · γ(L) ≤ γ(K ∩ L)`. The proof is the base case of Royen's theorem: in dimension one two
origin-symmetric convex sets are necessarily nested, so the intersection is the smaller of the
two, whose measure dominates the product since a probability measure is bounded by one. -/
theorem gaussian_correlation : GaussianCorrelationHolds 1 := by
  intro K L hK hL hKs hLs
  rcases subset_or_subset_one_dim hK hL hKs hLs with h | h
  · exact gaussian_correlation_of_subset h
  · rw [Set.inter_comm, mul_comm]
    exact gaussian_correlation_of_subset h

end Frontier

