/-
Basic definitions: Umegaki relative entropy and quantum channels in Kraus form.
-/
import Mathlib

namespace QI

open Matrix

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- The **Umegaki quantum relative entropy** `D(ρ‖σ) = Tr ρ (log ρ - log σ)`, where the
logarithm is the continuous functional calculus applied to a (Hermitian) matrix.
The value is extracted as a real number via the real part of the trace. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : ℝ :=
  (trace (ρ * cfc Real.log ρ)).re - (trace (ρ * cfc Real.log σ)).re

/-- A **quantum channel** (CPTP map) from `n × n` matrices to `m × m` matrices, presented by a
family of Kraus operators `K k : Matrix m n ℂ` satisfying `∑ k, (K k)ᴴ * K k = 1`.
By the Choi–Kraus theorem every completely positive trace preserving map between matrix
algebras is of this form. -/
structure Channel (ι n m : Type*) [Fintype ι] [Fintype n] [Fintype m] [DecidableEq n] where
  /-- The Kraus operators of the channel. -/
  kraus : ι → Matrix m n ℂ
  /-- The trace-preservation (completeness) relation. -/
  isTracePreserving : ∑ k, (kraus k)ᴴ * kraus k = 1

namespace Channel

variable (Φ : Channel ι n m)

/-- The action of a channel: `Φ(X) = ∑ k, K k * X * (K k)ᴴ`. -/
def map (X : Matrix n n ℂ) : Matrix m m ℂ := ∑ k, Φ.kraus k * X * (Φ.kraus k)ᴴ

/-- The adjoint (Heisenberg picture) map: `Φ*(Y) = ∑ k, (K k)ᴴ * Y * K k`.  It is unital. -/
def adj (Y : Matrix m m ℂ) : Matrix n n ℂ := ∑ k, (Φ.kraus k)ᴴ * Y * Φ.kraus k

end Channel

end QI

/-
Scalar integral representation underlying the integral formula for quantum relative entropy.

For `p q > 0`:
  `∫_0^∞  t (p-q)^2 / ((1+t)^2 (p + t q)) dt = p log p - p log q - (p - q)`.
-/
import Mathlib

namespace QI

open MeasureTheory Filter Topology Set

/-- The integrand `t ↦ t (p-q)² / ((1+t)² (p+tq))`. -/
noncomputable def sInt (p q t : ℝ) : ℝ := t * (p - q) ^ 2 / ((1 + t) ^ 2 * (p + t * q))

/-- An antiderivative of `sInt p q` on `[0, ∞)`. -/
noncomputable def sAnti (p q t : ℝ) : ℝ :=
  p * Real.log (1 + t) + (p - q) / (1 + t) - p * Real.log (p + t * q)

lemma hasDerivAt_sAnti {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (sAnti p q) (sInt p q t) t := by
  have h1 : (0:ℝ) < 1 + t := by linarith
  have h2 : (0:ℝ) < p + t * q := by nlinarith
  have d1 : HasDerivAt (fun t : ℝ => p * Real.log (1 + t)) (p * (1 / (1 + t))) t := by
    have : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    simpa [div_eq_inv_mul] using ((this.log h1.ne').const_mul p)
  have d2 : HasDerivAt (fun t : ℝ => (p - q) / (1 + t)) (-((p - q) / (1 + t) ^ 2)) t := by
    have : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    have := (this.inv h1.ne').const_mul (p - q)
    simpa [div_eq_mul_inv, mul_comm, mul_div_assoc] using this
  have d3 : HasDerivAt (fun t : ℝ => p * Real.log (p + t * q)) (p * (q / (p + t * q))) t := by
    have : HasDerivAt (fun t : ℝ => p + t * q) q t := by
      simpa using ((hasDerivAt_id t).mul_const q).const_add p
    simpa [div_eq_inv_mul, mul_comm] using ((this.log h2.ne').const_mul p)
  have := (d1.add d2).sub d3
  convert this using 1
  rw [sInt]
  field_simp
  ring

lemma sInt_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ sInt p q t := by
  have h1 : (0:ℝ) < 1 + t := by linarith
  have h2 : (0:ℝ) < p + t * q := by nlinarith
  apply div_nonneg (by positivity)
  positivity

lemma tendsto_denom {p q : ℝ} (hq : 0 < q) :
    Tendsto (fun t : ℝ => p + t * q) atTop atTop :=
  Filter.tendsto_atTop_add_const_left _ p (Filter.tendsto_id.atTop_mul_const hq)

lemma tendsto_sAnti {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (sAnti p q) atTop (𝓝 (-(p * Real.log q))) := by
  have hd := tendsto_denom (p := p) hq
  have h0 : Tendsto (fun t : ℝ => (q - p) / (q * (p + t * q))) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (Filter.Tendsto.const_mul_atTop hq hd) _
  have hr : Tendsto (fun t : ℝ => (1 + t) / (p + t * q)) atTop (𝓝 (1 / q)) := by
    have heq : ∀ᶠ t : ℝ in atTop, 1 / q + (q - p) / (q * (p + t * q)) = (1 + t) / (p + t * q) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      have h2 : (0:ℝ) < p + t * q := by positivity
      field_simp
      ring
    have := (tendsto_const_nhds (x := 1 / q) (f := atTop (α := ℝ))).add h0
    rw [add_zero] at this
    exact this.congr' heq
  have hlog : Tendsto (fun t : ℝ => p * Real.log ((1 + t) / (p + t * q))) atTop
      (𝓝 (p * Real.log (1 / q))) :=
    ((Real.continuousAt_log (by positivity)).tendsto.comp hr).const_mul p
  have hinv : Tendsto (fun t : ℝ => (p - q) / (1 + t)) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id) _
  have := hlog.add hinv
  rw [add_zero, Real.log_div one_ne_zero hq.ne', Real.log_one, zero_sub, mul_neg] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have h1 : (0:ℝ) < 1 + t := by linarith
  have h2 : (0:ℝ) < p + t * q := by positivity
  rw [sAnti, Real.log_div h1.ne' h2.ne']
  ring

lemma continuousWithinAt_sAnti {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ContinuousWithinAt (sAnti p q) (Ici 0) 0 :=
  ((hasDerivAt_sAnti hp hq le_rfl).continuousAt).continuousWithinAt

lemma integrableOn_sInt {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (sInt p q) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (continuousWithinAt_sAnti hp hq)
    (fun x hx => hasDerivAt_sAnti hp hq (le_of_lt hx))
    (fun x hx => sInt_nonneg hp hq (le_of_lt hx)) (tendsto_sAnti hp hq)

lemma integral_sInt {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in Ioi (0:ℝ), sInt p q t = p * Real.log p - p * Real.log q - (p - q) := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_sAnti hp hq)
    (fun x hx => hasDerivAt_sAnti hp hq (le_of_lt hx))
    (fun x hx => sInt_nonneg hp hq (le_of_lt hx)) (tendsto_sAnti hp hq)
  rw [this, sAnti]
  simp
  ring

end QI

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

