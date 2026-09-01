/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- Number of intensive state variables of a `P`-phase, `C`-component system:
temperature and pressure, together with `C - 1` independent mole fractions in each
of the `P` phases. -/
def phaseVarCount (C P : ℕ) : ℕ := P * (C - 1) + 2

/-- Number of equilibrium constraints: for each of the `C` components, equality of its
chemical potential across the `P` phases gives `P - 1` independent equations. -/
def phaseConstraintCount (C P : ℕ) : ℕ := C * (P - 1)

/-- Arithmetic core of the phase rule: if the `C * (P - 1)` constraints are independent,
the solution dimension `k` satisfies `k = C - P + 2` (over `ℤ`, so that no truncation of
natural subtraction occurs). -/
theorem dof_count (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) (k : ℕ)
    (h : phaseConstraintCount C P + k = phaseVarCount C P) :
    (k : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  simp only [phaseConstraintCount, phaseVarCount, Nat.add_sub_cancel] at h
  have h' : ((c + 1) * q + k : ℤ) = ((q + 1) * c + 2 : ℤ) := by exact_mod_cast h
  push_cast
  linear_combination h'

/-- **Gibbs phase rule** as an affine-dimension count.

The intensive state of a system with `C` components and `P` phases is described by
`phaseVarCount C P = P * (C - 1) + 2` real variables, subject to
`phaseConstraintCount C P = C * (P - 1)` equilibrium conditions, encoded here by an
arbitrary linear map `L` with an arbitrary right-hand side `b`.  Assuming the
constraints are independent (`L` surjective), the equilibrium set `{x | L x = b}` is a
nonempty affine subspace: it is a translate of `ker L`, and its dimension (the number of
degrees of freedom) is

  `F = C - P + 2`.

The dimension computation is `LinearMap.finrank_range_add_finrank_ker` (rank–nullity). -/
theorem gibbs_phase_rule (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (L : (Fin (phaseVarCount C P) → ℝ) →ₗ[ℝ] (Fin (phaseConstraintCount C P) → ℝ))
    (hL : Function.Surjective L) (b : Fin (phaseConstraintCount C P) → ℝ) :
    (∃ x₀ : Fin (phaseVarCount C P) → ℝ,
        {x | L x = b} = (fun v => x₀ + v) '' (LinearMap.ker L : Set (Fin (phaseVarCount C P) → ℝ)))
      ∧ (Module.finrank ℝ (LinearMap.ker L) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  constructor
  · obtain ⟨x₀, hx₀⟩ := hL b
    refine ⟨x₀, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · intro hx
      exact ⟨x - x₀, by simp [map_sub, hx, hx₀], by ring⟩
    · rintro ⟨v, hv, rfl⟩
      simp [map_add, hv, hx₀]
  · have hrange : Module.finrank ℝ (LinearMap.range L) = phaseConstraintCount C P := by
      rw [LinearMap.range_eq_top.2 hL]
      simp
    have hkey := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, Module.finrank_fin_fun] at hkey
    exact dof_count C P hC hP _ hkey

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

