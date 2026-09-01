/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-! ## Configuration space -/

/-- Physical three dimensional space. -/
abbrev Space : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The many body Coulomb energy

For `N` electrons (unit negative charge) at positions `x 0, …, x (N-1)` and `K` nuclei of
charges `z 0, …, z (K-1)` at positions `R 0, …, R (K-1)`, the classical Coulomb energy is

`W = ∑_{i<j} 1/|xᵢ - xⱼ| - ∑_{i,k} z_k/|xᵢ - R_k| + ∑_{k<l} z_k z_l/|R_k - R_l|`.

This is the potential part of the Hamiltonian appearing in the stability of matter problem. -/
noncomputable def coulombEnergy {N K : ℕ} (z : Fin K → ℝ)
    (x : Fin N → Space) (R : Fin K → Space) : ℝ :=
  (∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), 1 / dist (x p.1) (x p.2))
    - (∑ i : Fin N, ∑ k : Fin K, z k / dist (x i) (R k))
    + (∑ q ∈ Finset.univ.filter (fun q : Fin K × Fin K => q.1 < q.2),
        z q.1 * z q.2 / dist (R q.1) (R q.2))

/-- Sanity check on the definition: one electron and one nucleus of charge `z` give the
hydrogenic potential energy `-z/|x - R|`. -/
theorem coulombEnergy_one_one (z₀ : ℝ) (x₀ R₀ : Space) :
    coulombEnergy (fun _ : Fin 1 => z₀) (fun _ : Fin 1 => x₀) (fun _ : Fin 1 => R₀)
      = -(z₀ / dist x₀ R₀) := by
  simp [coulombEnergy]

/-- With no electrons present the Coulomb energy of a system of nuclei with nonnegative
charges is nonnegative. -/
theorem coulombEnergy_nonneg_of_no_electrons {K : ℕ} (z : Fin K → ℝ) (hz : ∀ k, 0 ≤ z k)
    (R : Fin K → Space) :
    0 ≤ coulombEnergy z (fun _ : Fin 0 => (0 : Space)) R := by
  have h : (0 : ℝ) ≤ ∑ q ∈ Finset.univ.filter (fun q : Fin K × Fin K => q.1 < q.2),
      z q.1 * z q.2 / dist (R q.1) (R q.2) := by
    refine Finset.sum_nonneg ?_
    intro q _
    exact div_nonneg (mul_nonneg (hz _) (hz _)) dist_nonneg
  simpa [coulombEnergy] using h

/-! ## The analytic core: a weighted arithmetic–geometric mean bound

The Lieb–Thirring kinetic energy inequality controls the kinetic energy from below by
`c_LT * ∫ ρ^{5/3}`, while the electrostatic (Baxter / Lieb–Yau) inequality together with
Hölder's inequality controls the Coulomb energy from below by
`-c_B * (∫ ρ^{5/3})^{3/5} * D^{2/5}`, where `D` is a screening integral bounded by a constant
times the number of particles.  Stability then follows from the elementary optimisation
`a t - b t^{3/5} d^{2/5} ≥ -C d`, which is the content of the next two lemmas. -/

/-- A scaled weighted AM–GM bound: for every `lam > 0` and nonnegative `t`, `d`,
`t^{3/5} d^{2/5} ≤ (3/5) lam t + (2/5) lam^{-3/2} d`. -/
theorem rpow_three_fifths_two_fifths_le (lam t d : ℝ) (hlam : 0 < lam)
    (ht : 0 ≤ t) (hd : 0 ≤ d) :
    t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5)
      ≤ (3 / 5) * (lam * t) + (2 / 5) * (lam ^ (-(3 : ℝ) / 2) * d) := by
  have hlam' : (0 : ℝ) ≤ lam := hlam.le
  have hp₁ : (0 : ℝ) ≤ lam * t := mul_nonneg hlam' ht
  have hp₂ : (0 : ℝ) ≤ lam ^ (-(3 : ℝ) / 2) * d :=
    mul_nonneg (Real.rpow_nonneg hlam' _) hd
  have key := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0:ℝ) ≤ 3/5) (by norm_num : (0:ℝ) ≤ 2/5) hp₁ hp₂ (by norm_num)
  have hrw : (lam * t) ^ ((3:ℝ)/5) * (lam ^ (-(3 : ℝ) / 2) * d) ^ ((2:ℝ)/5)
      = t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5) := by
    rw [Real.mul_rpow hlam' ht, Real.mul_rpow (Real.rpow_nonneg hlam' _) hd,
      ← Real.rpow_mul hlam']
    have : lam ^ ((3:ℝ)/5) * lam ^ ((-(3 : ℝ) / 2) * ((2:ℝ)/5)) = 1 := by
      rw [← Real.rpow_add hlam]
      norm_num
    calc lam ^ ((3:ℝ)/5) * t ^ ((3:ℝ)/5) * (lam ^ ((-(3 : ℝ) / 2) * ((2:ℝ)/5)) * d ^ ((2:ℝ)/5))
        = (lam ^ ((3:ℝ)/5) * lam ^ ((-(3 : ℝ) / 2) * ((2:ℝ)/5)))
            * (t ^ ((3:ℝ)/5) * d ^ ((2:ℝ)/5)) := by ring
      _ = t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5) := by rw [this, one_mul]
  rw [hrw] at key
  exact key

/-- The elementary optimisation underlying the passage from the Lieb–Thirring inequality to
stability: for `a, b > 0` and `t, d ≥ 0`,
`a t - b t^{3/5} d^{2/5} ≥ - (2/5) b (5a/(3b))^{-3/2} d`. -/
theorem sub_rpow_ge (a b t d : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) (hd : 0 ≤ d) :
    -((2 / 5) * b * ((5 * a) / (3 * b)) ^ (-(3 : ℝ) / 2) * d)
      ≤ a * t - b * (t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5)) := by
  set lam : ℝ := (5 * a) / (3 * b) with hlamdef
  have hlam : 0 < lam := by
    have : (0:ℝ) < 3 * b := by linarith
    exact div_pos (by linarith) this
  have hAMGM := rpow_three_fifths_two_fifths_le lam t d hlam ht hd
  have hmul : b * (t ^ ((3 : ℝ) / 5) * d ^ ((2 : ℝ) / 5))
      ≤ b * ((3 / 5) * (lam * t) + (2 / 5) * (lam ^ (-(3 : ℝ) / 2) * d)) :=
    mul_le_mul_of_nonneg_left hAMGM hb.le
  have hcoef : b * ((3 / 5) * lam) = a := by
    rw [hlamdef]
    field_simp
  nlinarith [hmul, hcoef]

/-! ## Stability of matter -/

/-- The explicit stability constant produced by the reduction: it depends only on the
Lieb–Thirring constant `cLT`, the electrostatic constant `cB` and the screening constant
`cScr`. -/
noncomputable def stabilityConstant (cLT cB cScr : ℝ) : ℝ :=
  (2 / 5) * cB * ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) * cScr

/--
**Stability of matter from the Lieb–Thirring inequality (Lean-checked reduction).**

Consider `N` electrons at positions `x` and `K` nuclei of charges `z` at positions `R`,
and let `T` be the kinetic energy of the electronic state, `S = ∫ ρ^{5/3}` the
Lieb–Thirring functional of its one-particle density, and `D` the screening quantity
appearing in the electrostatic estimate.  Assume:

* `hkin`  — the **Lieb–Thirring kinetic energy inequality** `T ≥ cLT * S`
  (this is where the Pauli principle enters);
* `hpot`  — the **electrostatic inequality** (Baxter / Lieb–Yau, combined with Hölder)
  `W ≥ -cB * S^{3/5} * D^{2/5}` for the many body Coulomb energy `W`;
* `hscr`  — the **screening bound** `D ≤ cScr * (N + K)`.

Then the total energy is bounded below *linearly in the number of particles*:

`T + W ≥ - stabilityConstant cLT cB cScr * (N + K)`,

which is exactly stability of matter of the second kind.  The three hypotheses are the
hard analytic inputs; the present theorem is the fully verified derivation of stability
from them, including the sharp form of the optimisation constant.
-/
theorem lieb_thirring_stability {N K : ℕ} (z : Fin K → ℝ)
    (x : Fin N → Space) (R : Fin K → Space)
    (T S D cLT cB cScr : ℝ)
    (hcLT : 0 < cLT) (hcB : 0 < cB)
    (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hkin : cLT * S ≤ T)
    (hpot : -(cB * (S ^ ((3 : ℝ) / 5) * D ^ ((2 : ℝ) / 5))) ≤ coulombEnergy z x R)
    (hscr : D ≤ cScr * ((N : ℝ) + K)) :
    -(stabilityConstant cLT cB cScr * ((N : ℝ) + K)) ≤ T + coulombEnergy z x R := by
  have hopt := sub_rpow_ge cLT cB S D hcLT hcB hS hD
  have hconst : (0 : ℝ) ≤ (2 / 5) * cB * ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hmono : (2 / 5) * cB * ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) * D
      ≤ (2 / 5) * cB * ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) * (cScr * ((N : ℝ) + K)) :=
    mul_le_mul_of_nonneg_left hscr hconst
  have hstab : stabilityConstant cLT cB cScr * ((N : ℝ) + K)
      = (2 / 5) * cB * ((5 * cLT) / (3 * cB)) ^ (-(3 : ℝ) / 2) * (cScr * ((N : ℝ) + K)) := by
    simp [stabilityConstant]; ring
  rw [hstab]
  linarith [hopt, hpot, hkin, hmono]

/-- Non-vacuity check: the hypotheses of `lieb_thirring_stability` are simultaneously
satisfiable in a genuinely interacting configuration (one electron and one unit-charge
nucleus at distance one, with a nonzero, in fact negative, Coulomb energy). -/
theorem lieb_thirring_stability_hypotheses_satisfiable (x₀ R₀ : Space)
    (hdist : dist x₀ R₀ = 1) :
    ∃ T S D cLT cB cScr : ℝ,
      0 < cLT ∧ 0 < cB ∧ 0 ≤ S ∧ 0 ≤ D ∧ cLT * S ≤ T ∧
      -(cB * (S ^ ((3 : ℝ) / 5) * D ^ ((2 : ℝ) / 5)))
        ≤ coulombEnergy (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => x₀) (fun _ : Fin 1 => R₀) ∧
      D ≤ cScr * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) ∧
      coulombEnergy (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => x₀) (fun _ : Fin 1 => R₀) < 0 := by
  refine ⟨1, 1, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ?_, by norm_num, ?_⟩
  · rw [coulombEnergy_one_one, hdist]
    norm_num
  · rw [coulombEnergy_one_one, hdist]
    norm_num

/-- Reformulation: the energy per particle is bounded below by a universal constant,
i.e. the system does not collapse as the number of particles grows. -/
theorem lieb_thirring_stability_per_particle {N K : ℕ} (z : Fin K → ℝ)
    (x : Fin N → Space) (R : Fin K → Space)
    (T S D cLT cB cScr : ℝ)
    (hcLT : 0 < cLT) (hcB : 0 < cB)
    (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hkin : cLT * S ≤ T)
    (hpot : -(cB * (S ^ ((3 : ℝ) / 5) * D ^ ((2 : ℝ) / 5))) ≤ coulombEnergy z x R)
    (hscr : D ≤ cScr * ((N : ℝ) + K))
    (hpos : 0 < (N : ℝ) + K) :
    -stabilityConstant cLT cB cScr ≤ (T + coulombEnergy z x R) / ((N : ℝ) + K) := by
  have h := lieb_thirring_stability z x R T S D cLT cB cScr hcLT hcB hS hD hkin hpot hscr
  rw [le_div_iff₀ hpos]
  linarith [h]

end Frontier

