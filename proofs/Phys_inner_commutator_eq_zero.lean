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

/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- the requested header, reproduced verbatim as a module docstring immediately after the import.)

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-! ## The abstract (operator) virial theorem -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- In a stationary state, the expectation value of any commutator with the Hamiltonian
vanishes: `⟨ψ, [H, A] ψ⟩ = 0` whenever `H` is symmetric and `H ψ = E₀ ψ` with `E₀` real. -/
lemma inner_commutator_eq_zero (H A : E →ₗ[ℂ] E) (ψ : E) (E₀ : ℝ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (heig : H ψ = (E₀ : ℂ) • ψ) :
    (inner ℂ ψ (H (A ψ) - A (H ψ)) : ℂ) = 0 := by
  rw [inner_sub_right, ← hsymm, heig]
  simp only [inner_smul_left, map_smul, inner_smul_right, Complex.conj_ofReal]
  ring

/-- **Quantum virial theorem.**

For a bound stationary state `ψ` of a symmetric Hamiltonian `H` with (real) energy `E₀`,
`H ψ = E₀ ψ`, and operators `T` (kinetic energy) and `W` (the virial `r · ∇V`) satisfying the
canonical commutator identity `[H, A] = 2T - W` for the dilation generator `A`
(`A = r · ∇ + d/2`, i.e. `i A = (r·p + p·r)/2`), one has `2⟨T⟩ = ⟨W⟩`. -/
theorem virial_theorem (H T W A : E →ₗ[ℂ] E) (ψ : E) (E₀ : ℝ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (heig : H ψ = (E₀ : ℂ) • ψ)
    (hcomm : ∀ x : E, H (A x) - A (H x) = (2 : ℂ) • T x - W x) :
    2 * inner ℂ ψ (T ψ) = inner ℂ ψ (W ψ) := by
  have key := inner_commutator_eq_zero H A ψ E₀ hsymm heig
  rw [hcomm ψ, inner_sub_right, inner_smul_right] at key
  linear_combination key

end Abstract

/-! ## The concrete one-dimensional Schrödinger commutator

We verify the commutator hypothesis of `Phys.virial_theorem` for the one-dimensional
Schrödinger operator `H = -½ d²/dx² + V`, with `T = -½ d²/dx²`, dilation generator
`A = x d/dx + ½` and virial `W = x V'(x)`. -/

section Concrete

/-- Kinetic energy operator in one dimension, `T = -½ d²/dx²`. -/
noncomputable def kin (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => -(1 / 2) * deriv (deriv ψ) x

/-- Schrödinger operator `H = -½ d²/dx² + V`. -/
noncomputable def ham (v ψ : ℝ → ℂ) : ℝ → ℂ := fun x => kin ψ x + v x * ψ x

/-- Generator of dilations, `A = x d/dx + ½`. -/
noncomputable def dil (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * deriv ψ x + ψ x / 2

/-- Virial operator `W = x V'(x)` (in one dimension, `r · ∇V`). -/
noncomputable def vir (v ψ : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * deriv v x * ψ x

private lemma hasDerivAt_coe (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
  simpa using Complex.ofRealCLM.hasDerivAt (x := x)

lemma hasDerivAt_dil {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (2 : ℕ) ψ) (x : ℝ) :
    HasDerivAt (dil ψ) ((3 / 2 : ℂ) * deriv ψ x + x * deriv (deriv ψ) x) x := by
  have h0 : HasDerivAt ψ (deriv ψ x) x := (hψ.differentiable (by norm_num) x).hasDerivAt
  have h1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    (ContDiff.differentiable_deriv_two hψ x).hasDerivAt
  have := ((hasDerivAt_coe x).mul h1).add (h0.div_const 2)
  convert this using 1
  ring

lemma deriv_dil {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (2 : ℕ) ψ) :
    deriv (dil ψ) = fun x => (3 / 2 : ℂ) * deriv ψ x + x * deriv (deriv ψ) x :=
  funext fun x => (hasDerivAt_dil hψ x).deriv

lemma deriv_deriv_dil {ψ : ℝ → ℂ} (hψ : ContDiff ℝ (3 : ℕ) ψ) (x : ℝ) :
    deriv (deriv (dil ψ)) x =
      (5 / 2 : ℂ) * deriv (deriv ψ) x + x * deriv (deriv (deriv ψ)) x := by
  have hψ2 : ContDiff ℝ (2 : ℕ) ψ := hψ.of_le (by exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))
  have hd1 : ContDiff ℝ (2 : ℕ) (deriv ψ) := by
    have := (contDiff_succ_iff_deriv (n := ((2:ℕ) : WithTop ℕ∞)) (f := ψ)).mp
      (by norm_num; exact hψ)
    simpa using this.2.2
  have h1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x :=
    (ContDiff.differentiable_deriv_two hψ2 x).hasDerivAt
  have h2 : HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) x) x :=
    (ContDiff.differentiable_deriv_two hd1 x).hasDerivAt
  rw [deriv_dil hψ2]
  have : HasDerivAt (fun y : ℝ => (3 / 2 : ℂ) * deriv ψ y + y * deriv (deriv ψ) y)
      ((5 / 2 : ℂ) * deriv (deriv ψ) x + x * deriv (deriv (deriv ψ)) x) x := by
    have := (h1.const_mul (3 / 2 : ℂ)).add ((hasDerivAt_coe x).mul h2)
    convert this using 1
    ring
  exact this.deriv

lemma hasDerivAt_ham {v ψ : ℝ → ℂ} (hv : Differentiable ℝ v) (hψ : ContDiff ℝ (3 : ℕ) ψ) (x : ℝ) :
    HasDerivAt (ham v ψ)
      (-(1 / 2 : ℂ) * deriv (deriv (deriv ψ)) x + (deriv v x * ψ x + v x * deriv ψ x)) x := by
  have hψ2 : ContDiff ℝ (2 : ℕ) ψ := hψ.of_le (by exact_mod_cast (by norm_num : (2:ℕ) ≤ 3))
  have hd1 : ContDiff ℝ (2 : ℕ) (deriv ψ) := by
    have := (contDiff_succ_iff_deriv (n := ((2:ℕ) : WithTop ℕ∞)) (f := ψ)).mp
      (by norm_num; exact hψ)
    simpa using this.2.2
  have h0 : HasDerivAt ψ (deriv ψ x) x := (hψ.differentiable (by norm_num) x).hasDerivAt
  have h2 : HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) x) x :=
    (ContDiff.differentiable_deriv_two hd1 x).hasDerivAt
  have hvx : HasDerivAt v (deriv v x) x := (hv x).hasDerivAt
  show HasDerivAt (fun y => -(1 / 2 : ℂ) * deriv (deriv ψ) y + v y * ψ y) _ x
  exact (h2.const_mul (-(1 / 2 : ℂ))).add (hvx.mul h0)

lemma deriv_ham {v ψ : ℝ → ℂ} (hv : Differentiable ℝ v) (hψ : ContDiff ℝ (3 : ℕ) ψ) (x : ℝ) :
    deriv (ham v ψ) x =
      -(1 / 2 : ℂ) * deriv (deriv (deriv ψ)) x + (deriv v x * ψ x + v x * deriv ψ x) :=
  (hasDerivAt_ham hv hψ x).deriv

/-- The Schrödinger commutator identity `[H, A] = 2T - W` in one dimension, where
`H = -½ d²/dx² + V` is the Schrödinger operator, `A = x d/dx + ½` generates dilations,
`T = -½ d²/dx²` and `W = x V'(x)`. -/
theorem schrodinger_commutator {v ψ : ℝ → ℂ}
    (hv : Differentiable ℝ v) (hψ : ContDiff ℝ (3 : ℕ) ψ) (x : ℝ) :
    ham v (dil ψ) x - dil (ham v ψ) x = (2 : ℂ) * kin ψ x - vir v ψ x := by
  simp only [ham, kin, dil, vir, deriv_deriv_dil hψ, deriv_ham hv hψ]
  ring

end Concrete

end Phys

#print axioms Phys.virial_theorem
#print axioms Phys.schrodinger_commutator

