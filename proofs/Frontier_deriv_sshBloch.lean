/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is the chiral (off-diagonal) matrix
`[[0, h(k)], [conj (h k), 0]]`, so the spectral gap is open at `k` iff `h k ≠ 0`. -/
noncomputable def sshBloch (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * (k : ℂ))

/-- The winding number of the SSH model,
`W = (2π i)⁻¹ ∫_0^{2π} h'(k) / h(k) dk`, where `h` is `sshBloch`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∫ k in (0:ℝ)..(2 * Real.pi),
      (Complex.I * (w : ℂ) * Complex.exp (Complex.I * (k : ℂ))) / sshBloch v w k

/-- The derivative of the Bloch function `h(k) = v + w e^{ik}` is `i w e^{ik}`,
so the integrand of `sshWinding` is indeed the logarithmic derivative `h'/h`. -/
theorem deriv_sshBloch (v w : ℝ) (k : ℝ) :
    deriv (fun t : ℝ => sshBloch v w t) k
      = Complex.I * (w : ℂ) * Complex.exp (Complex.I * (k : ℂ)) := by
  have h : (fun t : ℝ => sshBloch v w t)
      = fun t : ℝ => (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * (t : ℝ)) := rfl
  rw [h]
  have hd : HasDerivAt (fun t : ℝ => (v : ℂ) + (w : ℂ) * Complex.exp (Complex.I * (t : ℝ)))
      (Complex.I * (w : ℂ) * Complex.exp (Complex.I * (k : ℂ))) k := by
    have h1 : HasDerivAt (fun t : ℝ => (Complex.I * (t : ℂ))) Complex.I k := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := k)).const_mul Complex.I
    have h2 := (h1.cexp).const_mul (w : ℂ)
    have h3 := h2.const_add ((v : ℂ))
    convert h3 using 1
    ring
  exact hd.deriv

/-- The gap of the SSH chain is open at every quasi-momentum iff `|v| ≠ w` (for `w > 0`). -/
theorem sshBloch_ne_zero (v w : ℝ) (hw : 0 < w) (hgap : |v| ≠ w) (k : ℝ) :
    sshBloch v w k ≠ 0 := by
  intro h
  have h' : (w : ℂ) * Complex.exp (Complex.I * (k : ℂ)) = -(v : ℂ) := by
    have := h
    unfold sshBloch at this
    linear_combination this
  have habs : ‖(w : ℂ) * Complex.exp (Complex.I * (k : ℂ))‖ = ‖(-(v : ℂ))‖ := by rw [h']
  rw [norm_mul] at habs
  have hexp : ‖Complex.exp (Complex.I * (k : ℂ))‖ = 1 := by
    rw [mul_comm]
    simp
  rw [hexp, mul_one, norm_neg, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hw] at habs
  exact hgap habs.symm

/-- The SSH winding integral is the contour integral of `z⁻¹` over the circle of radius `w`
centred at `v`: the Bloch loop `k ↦ v + w e^{ik}` is exactly that circle. -/
theorem sshWinding_eq_circleIntegral (v w : ℝ) :
    sshWinding v w = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C((v : ℂ), w), z⁻¹ := by
  unfold sshWinding
  congr 1
  rw [circleIntegral]
  refine intervalIntegral.integral_congr ?_
  intro k _
  simp only [deriv_circleMap, circleMap, smul_eq_mul, sshBloch]
  rw [div_eq_mul_inv]
  have : Complex.exp (Complex.I * (k : ℂ)) = Complex.exp ((k : ℂ) * Complex.I) := by
    rw [mul_comm]
  rw [this]
  ring_nf

/-- In the topological phase `|v| < w` the winding number equals `1`. -/
theorem sshWinding_topological (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball ((v : ℂ)) w := by
    simp only [Metric.mem_ball, dist_zero_left]
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hcirc : (∮ z in C((v : ℂ), w), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have := circleIntegral.integral_sub_inv_of_mem_ball hmem
    simpa using this
  rw [sshWinding_eq_circleIntegral, hcirc]
  have hpi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- In the trivial phase `w < |v|` the winding number equals `0`. -/
theorem sshWinding_trivial (v w : ℝ) (hw : 0 < w) (h : w < |v|) : sshWinding v w = 0 := by
  have hnot : ∀ z ∈ Metric.closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [Metric.mem_closedBall] at hz
    rw [hz0] at hz
    rw [dist_zero_left] at hz
    simp only [Complex.norm_real, Real.norm_eq_abs] at hz
    linarith
  have hcirc : (∮ z in C((v : ℂ), w), z⁻¹) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hw.le
      Set.countable_empty ?_ ?_
    · exact ContinuousOn.inv₀ continuousOn_id (fun z hz => hnot z hz)
    · intro z hz
      exact differentiableAt_inv (hnot z (Metric.ball_subset_closedBall hz.1))
  rw [sshWinding_eq_circleIntegral, hcirc, mul_zero]

/-- **SSH winding invariant.**  For a gapped SSH chain (`w > 0`, `|v| ≠ w`), the Bloch
Hamiltonian is nowhere degenerate, and the winding number
`W = (2π i)⁻¹ ∫_0^{2π} h'(k)/h(k) dk` of the Bloch loop `h(k) = v + w e^{ik}` is an
*integer*: it equals `1` in the topological phase `|v| < w` and `0` in the trivial phase
`|v| > w`.  Thus the topological phase of the SSH model is classified by a `ℤ`-valued
winding number, which is locally constant (constant on each of the two gapped phases). -/
theorem ssh_winding_invariant (v w : ℝ) (hw : 0 < w) (hgap : |v| ≠ w) :
    (∀ k : ℝ, sshBloch v w k ≠ 0) ∧
      ∃ n : ℤ, sshWinding v w = (n : ℂ) ∧ n = if |v| < w then 1 else 0 := by
  refine ⟨sshBloch_ne_zero v w hw hgap, ?_⟩
  rcases lt_or_gt_of_ne hgap with hlt | hgt
  · exact ⟨1, by simpa using sshWinding_topological v w hlt, by simp [hlt]⟩
  · exact ⟨0, by simpa using sshWinding_trivial v w hw hgt, by simp [not_lt.2 hgt.le]⟩

/-- Auxiliary sign-constancy: a continuous nowhere-vanishing function on `[0,1]` keeps its sign. -/
theorem sign_const_of_ne_zero_on_Icc (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (h0 : ∀ t ∈ Set.Icc (0:ℝ) 1, f t ≠ 0) :
    (f 0 < 0 ∧ f 1 < 0) ∨ (0 < f 0 ∧ 0 < f 1) := by
  have hz : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ho : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  rcases lt_or_gt_of_ne (h0 0 hz) with hf0 | hf0
  · refine Or.inl ⟨hf0, ?_⟩
    rcases lt_or_gt_of_ne (h0 1 ho) with hf1 | hf1
    · exact hf1
    · exfalso
      obtain ⟨c, hc, hc0⟩ :=
        intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf ⟨hf0.le, hf1.le⟩
      exact h0 c hc hc0
  · refine Or.inr ⟨hf0, ?_⟩
    rcases lt_or_gt_of_ne (h0 1 ho) with hf1 | hf1
    · exfalso
      obtain ⟨c, hc, hc0⟩ :=
        intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hf ⟨hf1.le, hf0.le⟩
      exact h0 c hc hc0
    · exact hf1

/-- **Homotopy invariance of the SSH winding number.**  Along any continuous path of SSH
parameters `t ↦ (v t, w t)` that stays gapped (`w t > 0` and `|v t| ≠ w t` for all `t ∈ [0,1]`),
the winding number is unchanged.  This is the precise sense in which the winding number is a
topological invariant of the gapped SSH chain. -/
theorem ssh_winding_homotopy_invariant (v w : ℝ → ℝ)
    (hv : ContinuousOn v (Set.Icc (0:ℝ) 1)) (hw : ContinuousOn w (Set.Icc (0:ℝ) 1))
    (hwpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < w t)
    (hgap : ∀ t ∈ Set.Icc (0:ℝ) 1, |v t| ≠ w t) :
    sshWinding (v 0) (w 0) = sshWinding (v 1) (w 1) := by
  have hz : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ho : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hcont : ContinuousOn (fun t => |v t| - w t) (Set.Icc (0:ℝ) 1) := (hv.abs).sub hw
  have hne : ∀ t ∈ Set.Icc (0:ℝ) 1, |v t| - w t ≠ 0 := fun t ht =>
    sub_ne_zero_of_ne (hgap t ht)
  rcases sign_const_of_ne_zero_on_Icc _ hcont hne with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [sshWinding_topological _ _ (by linarith [h0] : |v 0| < w 0),
      sshWinding_topological _ _ (by linarith [h1] : |v 1| < w 1)]
  · rw [sshWinding_trivial _ _ (hwpos 0 hz) (by linarith [h0] : w 0 < |v 0|),
      sshWinding_trivial _ _ (hwpos 1 ho) (by linarith [h1] : w 1 < |v 1|)]

end Frontier

