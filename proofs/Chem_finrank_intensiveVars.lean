/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- as a module docstring immediately after the import.)

import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Gibbs phase rule states that a system with `C` chemical components distributed over
`P` coexisting phases has

  `F = C - P + 2`

thermodynamic degrees of freedom.  The classical derivation is a dimension count:

* the intensive state of the system is described by the temperature `T`, the pressure `p`
  and the mole fractions `x j i` of component `i` in phase `j`, i.e. by a point of the
  `2 + P * C`-dimensional real vector space `Chem.IntensiveVars C P`;
* the state is subject to `P` normalisation constraints (one per phase, `∑ i, x j i = 1`)
  and to `C * (P - 1)` phase-equilibrium constraints (equality of the chemical potential of
  each component in consecutive phases), i.e. the constraints are the fibre of a linear map
  into the `P + (P - 1) * C`-dimensional space `Chem.ConstraintValues C P`;
* if the constraints are independent (the constraint map is surjective), the set of admissible
  states is an affine subspace whose direction is the kernel of the constraint map, and
  rank–nullity gives
  `dim = (2 + P * C) - (P + (P - 1) * C) = C - P + 2`.

`Chem.gibbs_phase_rule` is exactly this statement.  `Chem.constraintMap` provides the
concrete (linearised) thermodynamic constraint map, and
`Chem.gibbs_phase_rule_one_component_two_phases` instantiates everything in the
one-component/two-phase case (a coexistence curve, `F = 1`), showing that the independence
hypothesis is not vacuous.
-/

open Module

namespace Chem

/-- Intensive state variables of a `C`-component, `P`-phase system: the temperature, the
pressure, and the mole fraction `x j i` of component `i` in phase `j`. -/
abbrev IntensiveVars (C P : ℕ) : Type := ℝ × ℝ × (Fin P → Fin C → ℝ)

/-- Values of the constraints imposed on a `C`-component, `P`-phase system: one normalisation
constraint per phase, and, for each of the `P - 1` consecutive pairs of phases, one
phase-equilibrium constraint per component. -/
abbrev ConstraintValues (C P : ℕ) : Type := (Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)

theorem finrank_intensiveVars (C P : ℕ) :
    finrank ℝ (IntensiveVars C P) = 2 + P * C := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype]
  simp
  ring

theorem finrank_constraintValues (C P : ℕ) :
    finrank ℝ (ConstraintValues C P) = P + (P - 1) * C := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp

/-- The number of thermodynamic degrees of freedom of a system whose constraints are described
by the linear map `A`: the dimension of the direction (kernel) of the affine solution set. -/
noncomputable def degreesOfFreedom {C P : ℕ}
    (A : IntensiveVars C P →ₗ[ℝ] ConstraintValues C P) : ℕ :=
  finrank ℝ (LinearMap.ker A)

/-- **Gibbs phase rule.**  For a system of `C` components in `P ≥ 1` phases whose constraints
(`P` normalisations and `C * (P - 1)` phase equilibria) are independent, i.e. given by a
surjective linear map `A` on the space of intensive variables, the number of degrees of
freedom — the affine dimension of the set of admissible states — is `F = C - P + 2`. -/
theorem gibbs_phase_rule {C P : ℕ} (hP : 1 ≤ P)
    (A : IntensiveVars C P →ₗ[ℝ] ConstraintValues C P) (hA : Function.Surjective A) :
    (degreesOfFreedom A : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  have hrange : finrank ℝ (LinearMap.range A) = finrank ℝ (ConstraintValues C P) := by
    rw [LinearMap.range_eq_top.mpr hA]
    exact finrank_top ℝ _
  have hRN := LinearMap.finrank_range_add_finrank_ker A
  rw [hrange, finrank_constraintValues, finrank_intensiveVars] at hRN
  have h1 : ((P - 1 : ℕ) : ℤ) = (P : ℤ) - 1 := by omega
  have hRN' : ((P : ℤ) + ((P : ℤ) - 1) * C) + (degreesOfFreedom A : ℤ) = 2 + (P : ℤ) * C := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hRN
    push_cast [h1] at this
    simpa [degreesOfFreedom] using this
  nlinarith [hRN']

/-- The set of states satisfying the constraints with prescribed values `bb` is an affine
subspace: a translate of the kernel of the constraint map, whose dimension is the number of
degrees of freedom computed by `Chem.gibbs_phase_rule`. -/
theorem constraint_solution_set_eq {C P : ℕ}
    (A : IntensiveVars C P →ₗ[ℝ] ConstraintValues C P) (hA : Function.Surjective A)
    (bb : ConstraintValues C P) :
    ∃ v₀ : IntensiveVars C P,
      {v : IntensiveVars C P | A v = bb} = (fun w => v₀ + w) '' (LinearMap.ker A : Set _) := by
  obtain ⟨v₀, hv₀⟩ := hA bb
  refine ⟨v₀, ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨v - v₀, by simp [map_sub, h, hv₀], by abel⟩
  · rintro ⟨w, hw, rfl⟩
    simp [map_add, hw, hv₀]

/-- The concrete linearised thermodynamic constraint map.  For coefficients `a i j`, `b i j`,
`g i j` describing the (linearised) chemical potential
`μ i j = a i j * T + b i j * p + g i j * x j i`
of component `i` in phase `j`, the constraints are the total mole fraction `∑ i, x j i` of each
phase `j` together with the differences `μ i j - μ i (j+1)` of chemical potentials between
consecutive phases. -/
noncomputable def constraintMap {C P : ℕ} (a b g : Fin C → Fin P → ℝ) :
    IntensiveVars C P →ₗ[ℝ] ConstraintValues C P where
  toFun v :=
    (fun j => ∑ i, v.2.2 j i,
     fun j i =>
       (a i ⟨j, by omega⟩ * v.1 + b i ⟨j, by omega⟩ * v.2.1
          + g i ⟨j, by omega⟩ * v.2.2 ⟨j, by omega⟩ i)
       - (a i ⟨j + 1, by omega⟩ * v.1 + b i ⟨j + 1, by omega⟩ * v.2.1
          + g i ⟨j + 1, by omega⟩ * v.2.2 ⟨j + 1, by omega⟩ i))
  map_add' u v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => funext fun i => ?_)
    · simp [Finset.sum_add_distrib]
    · simp
      ring
  map_smul' c u := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => funext fun i => ?_)
    · simp [Finset.mul_sum]
    · simp
      ring

/-- Gibbs phase rule for the concrete linearised thermodynamic model: if the constraints of
`Chem.constraintMap a b g` are independent, the system has `C - P + 2` degrees of freedom. -/
theorem gibbs_phase_rule_constraintMap {C P : ℕ} (hP : 1 ≤ P) (a b g : Fin C → Fin P → ℝ)
    (h : Function.Surjective (constraintMap a b g)) :
    (degreesOfFreedom (constraintMap a b g) : ℤ) = (C : ℤ) - (P : ℤ) + 2 :=
  gibbs_phase_rule hP _ h

/-- A concrete one-component, two-phase system (chemical potentials `T + x` in the first phase
and `x` in the second) whose constraints are independent. -/
theorem surjective_constraintMap_one_two :
    Function.Surjective
      (constraintMap (C := 1) (P := 2) (fun _ j => if j = 0 then 1 else 0)
        (fun _ _ => 0) (fun _ _ => 1)) := by
  rintro ⟨c, d⟩
  refine ⟨(d 0 0 - c 0 + c 1, 0, fun j _ => c j), ?_⟩
  refine Prod.ext ?_ ?_
  · funext j; simp [constraintMap]
  · funext j i
    have hj : j = 0 := Fin.ext (by omega)
    have hi : i = 0 := Fin.ext (by omega)
    subst hj; subst hi
    simp [constraintMap]
    ring

/-- Non-vacuity of the phase rule: for one component in two phases the count gives exactly one
degree of freedom (a coexistence curve in the `(T, p)`-plane). -/
theorem gibbs_phase_rule_one_component_two_phases :
    (degreesOfFreedom
      (constraintMap (C := 1) (P := 2) (fun _ j => if j = 0 then 1 else 0)
        (fun _ _ => 0) (fun _ _ => 1)) : ℤ) = 1 := by
  have := gibbs_phase_rule_constraintMap (C := 1) (P := 2) (by norm_num) _ _ _
    surjective_constraintMap_one_two
  simpa using this

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

