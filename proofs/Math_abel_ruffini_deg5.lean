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

import Archive.Wiedijk100Theorems.AbelRuffini
/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial AbelRuffini

open scoped Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- **Abel–Ruffini for the quintic.**

There is a monic quintic polynomial over `ℚ` (namely `X ^ 5 - 4 * X + 2`) which is irreducible,
whose Galois group is *not* solvable, which has a complex root, and none of whose complex roots
is solvable by radicals.  Hence the general quintic equation cannot be solved by radicals.

The ingredients are Mathlib's `solvableByRad.isSolvable'`,
`Polynomial.Gal.galActionHom_bijective_of_prime_degree'` and `Equiv.Perm.not_solvable`,
packaged in `Archive.Wiedijk100Theorems.AbelRuffini`. -/
theorem Math.abel_ruffini_deg5 :
    ∃ p : ℚ[X], p.Monic ∧ p.natDegree = 5 ∧ Irreducible p ∧ ¬ IsSolvable p.Gal ∧
      (∃ x : ℂ, aeval x p = 0) ∧ ∀ x : ℂ, aeval x p = 0 → ¬ IsSolvableByRad ℚ x := by
  have h_irred : Irreducible (Φ ℚ 4 2) := irreducible_Phi 4 2 2 Nat.prime_two (by norm_num)
    (by norm_num) (by decide)
  refine ⟨Φ ℚ 4 2, monic_Phi 4 2, natDegree_Phi 4 2, h_irred, ?_, ?_, ?_⟩
  · intro h
    refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
      (solvable_of_surjective (gal_Phi 4 2 (by norm_num) h_irred).2)
    rw_mod_cast [Cardinal.mk_fintype, complex_roots_Phi 4 2 h_irred.separable]
  · obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
    rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
    exact ⟨x, hx⟩
  · exact fun x hx => not_solvable_by_rad' x hx

