import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- Four–dimensional Minkowski spacetime, as a real vector space. -/
abbrev Minkowski : Type := Fin 4 → ℝ

/-- The Minkowski bilinear form of signature `(+,-,-,-)`. -/
def mink (x y : Minkowski) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/-- A linear map of Minkowski space is a *proper Lorentz transformation* when it preserves the
Minkowski form and has determinant `1`. -/
def IsProperLorentz (L : Minkowski →ₗ[ℝ] Minkowski) : Prop :=
  (∀ x y, mink (L x) (L y) = mink x y) ∧ LinearMap.det L = 1

/-- The total spacetime reflection `PT : x ↦ -x`. -/
def PT : Minkowski →ₗ[ℝ] Minkowski := -LinearMap.id

@[simp] lemma PT_apply (x : Minkowski) : PT x = -x := rfl

/-- The dimension of Minkowski space is `4`. -/
lemma finrank_minkowski : Module.finrank ℝ Minkowski = 4 := by
  simp

/-- Total spacetime reflection is a proper Lorentz transformation: it preserves the Minkowski
form, and since spacetime is even dimensional its determinant is `(-1)^4 = 1`.  This is the
group-theoretic heart of the CPT theorem: `PT` lies in the proper Lorentz group (indeed, in the
identity component of the complex Lorentz group). -/
theorem isProperLorentz_PT : IsProperLorentz PT := by
  constructor
  · intro x y
    simp [mink]
  · have h : PT = (-1 : ℝ) • (LinearMap.id : Minkowski →ₗ[ℝ] Minkowski) := by
      ext x i; simp [PT]
    rw [h, LinearMap.det_smul, finrank_minkowski, LinearMap.det_id]
    norm_num

/--
A (bosonic, scalar) Wightman theory of `n`-point functions, packaged with the two axioms that
enter the CPT theorem:

* `lorentz_invariance`: the `n`-point function is invariant under proper Lorentz transformations
  applied simultaneously to all arguments.  (In the Wightman setting one first has invariance
  under the proper *orthochronous* group and then, by the Bargmann–Hall–Wightman theorem, under
  the whole proper complex Lorentz group, which contains `PT`; here we take the resulting
  invariance under all proper Lorentz transformations as the hypothesis.)
* `hermiticity`: the Wightman hermiticity axiom
  `W(x₁, …, xₙ)^* = W(xₙ, …, x₁)`, which encodes locality/positivity of the underlying field
  algebra in terms of the correlation functions.
-/
structure WightmanTheory (n : ℕ) where
  /-- The `n`-point Wightman function. -/
  W : (Fin n → Minkowski) → ℂ
  /-- Invariance under proper Lorentz transformations. -/
  lorentz_invariance :
    ∀ L : Minkowski →ₗ[ℝ] Minkowski, IsProperLorentz L →
      ∀ x : Fin n → Minkowski, W (fun i => L (x i)) = W x
  /-- Hermiticity: reversing the order of the arguments conjugates the Wightman function. -/
  hermiticity :
    ∀ x : Fin n → Minkowski, W (fun i => x (Fin.rev i)) = starRingEnd ℂ (W x)

/--
**CPT theorem** (statement form).

For any Lorentz-invariant local (Wightman) theory, the `n`-point functions satisfy the CPT
relation
`W(x₁, …, xₙ) = W(-xₙ, …, -x₁)^*`,
i.e. the theory is invariant under the antiunitary CPT operation: total spacetime reflection
`PT : x ↦ -x` combined with charge conjugation (complex conjugation of the correlators) and
reversal of the operator ordering.
-/
theorem cpt_theorem {n : ℕ} (T : WightmanTheory n) (x : Fin n → Minkowski) :
    T.W (fun i => -x (Fin.rev i)) = starRingEnd ℂ (T.W x) := by
  have h₁ : T.W (fun i => PT ((fun j => x (Fin.rev j)) i)) = T.W (fun j => x (Fin.rev j)) :=
    T.lorentz_invariance PT isProperLorentz_PT _
  simpa using h₁.trans (T.hermiticity x)

end Phys

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

