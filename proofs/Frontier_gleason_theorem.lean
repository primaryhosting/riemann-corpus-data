/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `Frontier.QuantumMeasure` : a quantum measure (frame function) on a complex Hilbert space.
* `Frontier.DensityOperator` : a positive semidefinite self-adjoint operator of trace one.
* `Frontier.gleason_theorem` : Gleason's theorem in the form of a Lean-checked reduction —
  granting the analytic core (the frame function theorem, valid in dimension `≥ 3`), every
  quantum measure is `x ↦ ⟪x, ρ x⟫` for a genuine density operator `ρ`.
* `Frontier.gleason_theorem_of_constant` : an unconditional base case (measures constant on
  the unit sphere, represented by the maximally mixed state).
* `Frontier.DensityOperator.toQuantumMeasure` : the (easy) converse direction.
* `Frontier.densityOperator_unique` : uniqueness of the representing density operator.

Mathlib does not contain Gleason's theorem.  The main Mathlib inputs used here are
`LinearMap.trace_eq_sum_inner` (trace as a sum over an orthonormal basis),
`stdOrthonormalBasis`, and `inner_map_self_eq_zero` (a complex operator with vanishing
quadratic form is zero).
-/

open scoped BigOperators

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A **quantum measure** (frame function) on a complex Hilbert space `E`:
a function on the unit sphere which is nonnegative and whose values sum to `1` along every
orthonormal basis.  This is the standard "probability assignment to rank one projections":
the value `toFun x` is the probability assigned to the projection onto `span x`. -/
structure QuantumMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The value of the measure on a unit vector, i.e. on the rank one projection it spans. -/
  toFun : E → ℝ
  /-- Nonnegativity on the unit sphere. -/
  nonneg : ∀ x : E, ‖x‖ = 1 → 0 ≤ toFun x
  /-- The values along any orthonormal basis add up to one. -/
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E, ∑ i, toFun (b i) = 1

/-- A **density operator**: a positive semidefinite self-adjoint operator of trace one. -/
structure DensityOperator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The underlying operator. -/
  op : E →ₗ[ℂ] E
  /-- Self-adjointness. -/
  isSymmetric : op.IsSymmetric
  /-- Positive semidefiniteness. -/
  nonneg : ∀ x : E, 0 ≤ (inner ℂ x (op x) : ℂ).re
  /-- Normalisation. -/
  trace_one : LinearMap.trace ℂ E op = 1

omit [FiniteDimensional ℂ E] in
/-- For a symmetric operator the quadratic form `⟪x, T x⟫` is real. -/
theorem inner_self_eq_re_of_isSymmetric {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (x : E) :
    (inner ℂ x (T x) : ℂ) = ((inner ℂ x (T x) : ℂ).re : ℝ) := by
  have h : (starRingEnd ℂ) (inner ℂ x (T x)) = inner ℂ x (T x) := by
    rw [inner_conj_symm]; exact hT x x
  simpa using (Complex.conj_eq_iff_re.mp h).symm

omit [FiniteDimensional ℂ E] in
/-- The quadratic form of an operator is homogeneous of degree two under real scaling. -/
theorem re_inner_smul_self (T : E →ₗ[ℂ] E) (c : ℝ) (x : E) :
    (inner ℂ ((c : ℂ) • x) (T ((c : ℂ) • x)) : ℂ).re = c ^ 2 * (inner ℂ x (T x) : ℂ).re := by
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp
  ring

omit [FiniteDimensional ℂ E] in
/-- An operator whose quadratic form is nonnegative on the unit sphere is positive
semidefinite. -/
theorem nonneg_of_nonneg_on_sphere {T : E →ₗ[ℂ] E}
    (h : ∀ x : E, ‖x‖ = 1 → 0 ≤ (inner ℂ x (T x) : ℂ).re) (x : E) :
    0 ≤ (inner ℂ x (T x) : ℂ).re := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
      rw [norm_smul]
      simp [inv_mul_cancel₀ hx']
    have hval := h _ hnu
    rw [re_inner_smul_self] at hval
    have hpos : (0:ℝ) < (‖x‖⁻¹) ^ 2 := by positivity
    nlinarith [hval]

/-- **Gleason's theorem** (Lean-checked reduction).

Let `E` be a complex Hilbert space of dimension at least three and let `μ` be a quantum
measure (frame function) on `E`.  Granting the analytic core of Gleason's theorem — the
*frame function theorem*, which states that every quantum measure on such a space is given
by a symmetric quadratic form (hypothesis `hquad`) — the measure `μ` is represented by a
genuine density operator `ρ`: `μ x = ⟪x, ρ x⟫` for every unit vector `x`.

What is proved here is the passage from a bare symmetric quadratic representation to a
*density operator*: positive semidefiniteness (from nonnegativity of `μ` on the sphere) and
unit trace (from the normalisation of `μ` along an orthonormal basis).

The hypothesis `h3 : 3 ≤ finrank ℂ E` is the dimension restriction of Gleason's theorem: it
is exactly what makes `hquad` true (the statement fails in dimension two), but it is not
used again once `hquad` is available. -/
theorem gleason_theorem (h3 : 3 ≤ Module.finrank ℂ E)
    (hquad : ∀ ν : QuantumMeasure E, ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧
      ∀ x : E, ‖x‖ = 1 → ν.toFun x = (inner ℂ x (T x) : ℂ).re)
    (μ : QuantumMeasure E) :
    ∃ ρ : DensityOperator E, ∀ x : E, ‖x‖ = 1 → μ.toFun x = (inner ℂ x (ρ.op x) : ℂ).re := by
  obtain ⟨T, hTsymm, hTrep⟩ := hquad μ
  have hpos : ∀ x : E, 0 ≤ (inner ℂ x (T x) : ℂ).re := by
    refine nonneg_of_nonneg_on_sphere (fun x hx => ?_)
    rw [← hTrep x hx]
    exact μ.nonneg x hx
  have htr : LinearMap.trace ℂ E T = 1 := by
    set b := stdOrthonormalBasis ℂ E with hb
    rw [LinearMap.trace_eq_sum_inner T b]
    have hterm : ∀ i, (inner ℂ (b i) (T (b i)) : ℂ) = ((μ.toFun (b i) : ℝ) : ℂ) := by
      intro i
      rw [inner_self_eq_re_of_isSymmetric hTsymm, hTrep (b i) (b.orthonormal.1 i)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Complex.ofReal_sum, μ.sum_eq_one b]
    norm_num
  exact ⟨⟨T, hTsymm, hpos, htr⟩, hTrep⟩

/-- **Base case of Gleason's theorem**, proved unconditionally: a quantum measure that is
constant on the unit sphere (equivalently, invariant under all unitaries) is represented by
the maximally mixed state `ρ = (1 / dim E) • id`. -/
theorem gleason_theorem_of_constant (h3 : 3 ≤ Module.finrank ℂ E) (μ : QuantumMeasure E)
    (hconst : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → μ.toFun x = μ.toFun y) :
    ∃ ρ : DensityOperator E, ∀ x : E, ‖x‖ = 1 → μ.toFun x = (inner ℂ x (ρ.op x) : ℂ).re := by
  set n : ℕ := Module.finrank ℂ E with hn
  have hn0 : 0 < n := by omega
  set b := stdOrthonormalBasis ℂ E with hb
  set c : ℝ := μ.toFun (b ⟨0, hn0⟩) with hc
  have hsum : ∑ _i : Fin n, c = 1 := by
    rw [← μ.sum_eq_one b]
    exact Finset.sum_congr rfl fun i _ =>
      hconst _ _ (b.orthonormal.1 _) (b.orthonormal.1 i)
  have hcn : (n : ℝ) * c = 1 := by simpa [mul_comm] using hsum
  have hcval : c = (n : ℝ)⁻¹ := by
    field_simp at hcn ⊢
    linarith [hcn]
  -- the maximally mixed density operator
  refine ⟨⟨((n : ℝ)⁻¹ : ℂ) • LinearMap.id, ?_, ?_, ?_⟩, ?_⟩
  · intro x y
    simp [inner_smul_left, inner_smul_right]
  · intro x
    have hxx : (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by simp
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, inner_smul_right, hxx,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  · rw [map_smul, LinearMap.trace_id, ← hn]
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    simp only [smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ hne]
    norm_num
  · intro x hx
    have hxx : (inner ℂ x x : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by simp
    rw [hconst x (b ⟨0, hn0⟩) hx (b.orthonormal.1 _), ← hc, hcval]
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, inner_smul_right, hxx, hx,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    norm_num

/-- The easy converse of Gleason's theorem: every density operator does define a quantum
measure. -/
noncomputable def DensityOperator.toQuantumMeasure (ρ : DensityOperator E) : QuantumMeasure E where
  toFun x := (inner ℂ x (ρ.op x) : ℂ).re
  nonneg x _ := ρ.nonneg x
  sum_eq_one b := by
    have h : LinearMap.trace ℂ E ρ.op = ∑ i, (inner ℂ (b i) (ρ.op (b i)) : ℂ) :=
      LinearMap.trace_eq_sum_inner ρ.op b
    have h2 : ((∑ i, (inner ℂ (b i) (ρ.op (b i)) : ℂ).re : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← ρ.trace_one, h]
      exact Finset.sum_congr rfl fun i _ =>
        (inner_self_eq_re_of_isSymmetric ρ.isSymmetric (b i)).symm
    exact_mod_cast h2

@[simp] theorem DensityOperator.toQuantumMeasure_apply (ρ : DensityOperator E) (x : E) :
    ρ.toQuantumMeasure.toFun x = (inner ℂ x (ρ.op x) : ℂ).re := rfl

/-- Uniqueness in Gleason's theorem: a quantum measure determines its density operator. -/
theorem densityOperator_unique {ρ σ : DensityOperator E}
    (h : ∀ x : E, ‖x‖ = 1 → (inner ℂ x (ρ.op x) : ℂ).re = (inner ℂ x (σ.op x) : ℂ).re) :
    ρ.op = σ.op := by
  have key : ∀ x : E, (inner ℂ x (ρ.op x) : ℂ).re = (inner ℂ x (σ.op x) : ℂ).re := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hnu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        simp [inv_mul_cancel₀ hx']
      have hval := h _ hnu
      rw [re_inner_smul_self, re_inner_smul_self] at hval
      have hne : ((‖x‖⁻¹) ^ 2 : ℝ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne hval
  have hsymm : (ρ.op - σ.op).IsSymmetric := ρ.isSymmetric.sub σ.isSymmetric
  have hzero : ∀ x : E, inner ℂ ((ρ.op - σ.op) x) x = 0 := by
    intro x
    have h1 : (inner ℂ x ((ρ.op - σ.op) x) : ℂ)
        = ((inner ℂ x ((ρ.op - σ.op) x) : ℂ).re : ℝ) :=
      inner_self_eq_re_of_isSymmetric hsymm x
    have h2 : (inner ℂ x ((ρ.op - σ.op) x) : ℂ).re = 0 := by
      rw [LinearMap.sub_apply, inner_sub_right]
      simp [key x]
    rw [hsymm x x, h1, h2]
    simp
  exact sub_eq_zero.mp ((inner_map_self_eq_zero (ρ.op - σ.op)).mp hzero)

end Frontier

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

