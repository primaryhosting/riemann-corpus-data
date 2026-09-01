/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Configuration space of one particle. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-- **Pointwise Young-type inequality behind stability of matter.**

For a nonnegative density value `a` and constants `K > 0`, `C`,
`C * a ^ (4/3) ≤ K * a ^ (5/3) + (C ^ 2 / (4 * K)) * a`.

This is the elementary interpolation `ρ^{4/3} ≤ ε ρ^{5/3} + c_ε ρ` with the optimal
constant `c_ε = C²/(4K)`: it is what converts a Lieb–Thirring kinetic-energy bound
(`T ≥ K ∫ ρ^{5/3}`) together with a Coulomb (Baxter-type) potential bound
(`V ≥ -C ∫ ρ^{4/3}`) into a lower bound proportional to the particle number `∫ ρ`. -/
theorem rpow_four_thirds_le (K C a : ℝ) (ha : 0 ≤ a) (hK : 0 < K) :
    C * a ^ ((4 : ℝ) / 3) ≤ K * a ^ ((5 : ℝ) / 3) + (C ^ 2 / (4 * K)) * a := by
  set u : ℝ := a ^ ((1 : ℝ) / 3) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg ha _
  have h4 : u ^ (4 : ℕ) = a ^ ((4 : ℝ) / 3) := by
    rw [hu, ← Real.rpow_natCast (a ^ ((1 : ℝ) / 3)) 4, ← Real.rpow_mul ha]; norm_num
  have h5 : u ^ (5 : ℕ) = a ^ ((5 : ℝ) / 3) := by
    rw [hu, ← Real.rpow_natCast (a ^ ((1 : ℝ) / 3)) 5, ← Real.rpow_mul ha]; norm_num
  have h3 : u ^ (3 : ℕ) = a := by
    rw [hu, ← Real.rpow_natCast (a ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul ha]; norm_num
  rw [← h4, ← h5, ← h3, ← sub_nonneg]
  have hid : K * u ^ 5 + C ^ 2 / (4 * K) * u ^ 3 - C * u ^ 4
      = (2 * K * u - C) ^ 2 * u ^ 3 / (4 * K) := by
    field_simp; ring
  rw [hid]
  positivity

/-- Integrated form of `Frontier.rpow_four_thirds_le`: the Coulomb-type functional
`C ∫ ρ^{4/3}` is dominated by the Thomas–Fermi kinetic functional `K ∫ ρ^{5/3}` plus a
multiple of the particle number `∫ ρ`. -/
theorem coulomb_le_kinetic_add_number
    (ρ : Space → ℝ) (K C : ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hK : 0 < K)
    (h53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)))
    (h43 : Integrable (fun x => ρ x ^ ((4 : ℝ) / 3)))
    (h1 : Integrable ρ) :
    C * ∫ x, ρ x ^ ((4 : ℝ) / 3)
      ≤ K * (∫ x, ρ x ^ ((5 : ℝ) / 3)) + (C ^ 2 / (4 * K)) * ∫ x, ρ x := by
  have hmono : (∫ x, C * ρ x ^ ((4 : ℝ) / 3))
      ≤ ∫ x, (K * ρ x ^ ((5 : ℝ) / 3) + (C ^ 2 / (4 * K)) * ρ x) := by
    refine integral_mono (h43.const_mul C) ((h53.const_mul K).add (h1.const_mul _)) ?_
    intro x
    exact rpow_four_thirds_le K C (ρ x) (hρ x) hK
  rwa [integral_const_mul, integral_add (h53.const_mul K) (h1.const_mul _),
    integral_const_mul, integral_const_mul] at hmono

/-- **Lieb–Thirring stability of matter (reduction).**

Let `ρ : ℝ³ → ℝ` be the (nonnegative, integrable) one-particle density of an `N`-particle
state, so that `∫ ρ = N`.  Assume

* the **Lieb–Thirring kinetic energy inequality**: the kinetic energy `T` of the state
  obeys `T ≥ K ∫ ρ^{5/3}` for some constant `K > 0` (this is the many-body form of the
  Lieb–Thirring inequality, valid for fermionic states in three dimensions);
* the **Coulomb energy bound**: the total (electron–nucleus, electron–electron,
  nucleus–nucleus) potential energy `V` obeys `V ≥ -C ∫ ρ^{4/3}` for some constant `C`
  (a Baxter/Lieb–Yau-type electrostatic estimate).

Then the total energy is bounded below *linearly in the particle number*:
`T + V ≥ -(C² / (4K)) * N`, i.e. matter is stable of the second kind.

The proof is the Lean-checked reduction of stability of matter to the two inputs above,
via the sharp interpolation `C ρ^{4/3} ≤ K ρ^{5/3} + (C²/(4K)) ρ`. -/
theorem lieb_thirring_stability
    (ρ : Space → ℝ) (N K C T V : ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hK : 0 < K)
    (h53 : Integrable (fun x => ρ x ^ ((5 : ℝ) / 3)))
    (h43 : Integrable (fun x => ρ x ^ ((4 : ℝ) / 3)))
    (h1 : Integrable ρ)
    (hN : ∫ x, ρ x = N)
    (hT : K * ∫ x, ρ x ^ ((5 : ℝ) / 3) ≤ T)
    (hV : -(C * ∫ x, ρ x ^ ((4 : ℝ) / 3)) ≤ V) :
    -(C ^ 2 / (4 * K)) * N ≤ T + V := by
  have key := coulomb_le_kinetic_add_number ρ K C hρ hK h53 h43 h1
  rw [hN] at key
  linarith

/-- Sanity check (non-vacuity): the hypotheses of `Frontier.lieb_thirring_stability` are
satisfiable, e.g. by the vacuum state `ρ = 0`, `N = 0`. -/
example (K : ℝ) (hK : 0 < K) (T V : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V) :
    -((1 : ℝ) ^ 2 / (4 * K)) * 0 ≤ T + V := by
  refine lieb_thirring_stability (fun _ => (0 : ℝ)) 0 K 1 T V (fun _ => le_rfl) hK ?_ ?_ ?_ ?_ ?_ ?_
  · simp [Real.zero_rpow]
  · simp [Real.zero_rpow]
  · exact integrable_zero Space ℝ volume
  · simp
  · simp [hT]
  · simp [hV]

end Frontier

