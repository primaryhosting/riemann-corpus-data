import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Elementary optimisation step

The Thomas–Fermi-type minimisation `t ↦ K t - A √t √N` used in the proof of stability of
matter. -/

/-- If `K > 0` and `A ≥ 0`, then `K t - A √(t N) ≥ -(A²/(4K)) N` for `t, N ≥ 0`. -/
theorem quadratic_lower_bound {K A t N : ℝ} (hK : 0 < K) (hA : 0 ≤ A)
    (ht : 0 ≤ t) (hN : 0 ≤ N) :
    -(A ^ 2 / (4 * K)) * N ≤ K * t - A * (Real.sqrt t * Real.sqrt N) := by
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have h0 : (0:ℝ) ≤ (2 * K * Real.sqrt t - A * Real.sqrt N) ^ 2 := sq_nonneg _
  rw [div_mul_eq_mul_div, neg_div, neg_le_sub_iff_le_add, div_le_iff₀ (by linarith)]
  nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg N]

/-! ## The interpolation (Hölder) step -/

/-- Hölder/Cauchy–Schwarz interpolation: for a nonnegative density `ρ`,
`∫ ρ^{4/3} ≤ (∫ ρ^{5/3})^{1/2} (∫ ρ)^{1/2}`. -/
theorem integral_rpow_four_thirds_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hmeas : AEMeasurable ρ μ)
    (h1 : Integrable ρ μ) (h53 : Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) μ) :
    ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ
      ≤ Real.sqrt (∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ) * Real.sqrt (∫ x, ρ x ∂μ) := by
  have hfsm : AEStronglyMeasurable (fun x => ρ x ^ (5 / 6 : ℝ)) μ :=
    (hmeas.rpow_const _).aestronglyMeasurable
  have hgsm : AEStronglyMeasurable (fun x => ρ x ^ (1 / 2 : ℝ)) μ :=
    (hmeas.rpow_const _).aestronglyMeasurable
  have hf2 : ∀ x, (ρ x ^ (5 / 6 : ℝ)) ^ (2 : ℕ) = ρ x ^ (5 / 3 : ℝ) := by
    intro x
    rw [← Real.rpow_natCast (ρ x ^ (5 / 6 : ℝ)) 2, ← Real.rpow_mul (hρ0 x)]
    norm_num
  have hg2 : ∀ x, (ρ x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = ρ x := by
    intro x
    rw [← Real.rpow_natCast (ρ x ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (hρ0 x)]
    norm_num
  have hf : MemLp (fun x => ρ x ^ (5 / 6 : ℝ)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hfsm]
    simpa only [hf2] using h53
  have hg : MemLp (fun x => ρ x ^ (1 / 2 : ℝ)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hgsm]
    simpa only [hg2] using h1
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (f := fun x => ρ x ^ (5 / 6 : ℝ)) (g := fun x => ρ x ^ (1 / 2 : ℝ))
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hρ0 x) _)
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hρ0 x) _)
      (by rwa [h2]) (by rwa [h2])
  have e1 : ∀ x, ρ x ^ (5 / 6 : ℝ) * ρ x ^ (1 / 2 : ℝ) = ρ x ^ (4 / 3 : ℝ) := by
    intro x
    rw [← Real.rpow_add' (hρ0 x) (by norm_num)]
    norm_num
  have e2 : ∀ x, (ρ x ^ (5 / 6 : ℝ)) ^ (2 : ℝ) = ρ x ^ (5 / 3 : ℝ) := by
    intro x; rw [← Real.rpow_mul (hρ0 x)]; norm_num
  have e3 : ∀ x, (ρ x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = ρ x := by
    intro x; rw [← Real.rpow_mul (hρ0 x)]; norm_num
  simp only [e1, e2, e3] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert key using 3 <;> norm_num

/-! ## Stability of matter from the Lieb–Thirring kinetic energy inequality -/

/-- **Stability of matter, reduced to the Lieb–Thirring kinetic energy inequality.**

Let `ρ ≥ 0` be the one-particle density of a state of an `N`-particle system, i.e.
`∫ ρ = N`.  Assume:

* the *Lieb–Thirring kinetic energy inequality* `hLT`, which bounds the kinetic energy `T`
  of the state from below by `K ∫ ρ^{5/3}` (`K > 0`);
* an *electrostatic bound* `hCoul`, which bounds the total potential (Coulomb) energy `W`
  from below by `-A ∫ ρ^{4/3} - B N` (`A ≥ 0`), as provided by the Baxter/Lieb–Yau type
  electrostatic inequalities.

Then the total energy is bounded below *linearly in the particle number*:
`T + W ≥ -(A²/(4K) + B) N`, which is stability of matter of the second kind. -/
theorem lieb_thirring_stability {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ} {K A B N T W : ℝ}
    (hK : 0 < K) (hA : 0 ≤ A)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hmeas : AEMeasurable ρ μ)
    (h1 : Integrable ρ μ) (h53 : Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) μ)
    (hN : ∫ x, ρ x ∂μ = N)
    (hLT : K * ∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ ≤ T)
    (hCoul : -(A * ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ) - B * N ≤ W) :
    -(A ^ 2 / (4 * K) + B) * N ≤ T + W := by
  set t : ℝ := ∫ x, ρ x ^ (5 / 3 : ℝ) ∂μ with ht_def
  have ht0 : 0 ≤ t := integral_nonneg fun x => Real.rpow_nonneg (hρ0 x) _
  have hN0 : 0 ≤ N := hN ▸ integral_nonneg hρ0
  have hholder : ∫ x, ρ x ^ (4 / 3 : ℝ) ∂μ ≤ Real.sqrt t * Real.sqrt N := by
    have := integral_rpow_four_thirds_le hρ0 hmeas h1 h53
    rwa [hN] at this
  have hmain := quadratic_lower_bound (K := K) (A := A) (t := t) (N := N) hK hA ht0 hN0
  nlinarith [mul_le_mul_of_nonneg_left hholder hA]

/-! ## A base case: the classical (phase-space) Lieb–Thirring constant in dimension one

For `γ = 1`, `d = 1` the semiclassical phase-space integral is
`(2π)⁻¹ ∫_{ℝ} (p² - λ)_- dp = (2/(3π)) λ^{3/2}`, i.e. `L^cl_{1,1} = 2/(3π)`. -/
theorem classical_lieb_thirring_constant_one_dim {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 / (2 * Real.pi)) *
        ∫ p in (-Real.sqrt lam)..(Real.sqrt lam), (lam - p ^ 2)
      = (2 / (3 * Real.pi)) * lam ^ (3 / 2 : ℝ) := by
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam
  have hint : ∫ p in (-Real.sqrt lam)..(Real.sqrt lam), (lam - p ^ 2)
      = (4 / 3) * lam * Real.sqrt lam := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _)]
    rw [integral_const, integral_pow]
    simp only [smul_eq_mul]
    ring_nf
    nlinarith [hs, Real.sqrt_nonneg lam]
  rw [hint]
  have hpow : lam ^ (3 / 2 : ℝ) = lam * Real.sqrt lam := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hlam (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpow]
  ring

end Frontier

