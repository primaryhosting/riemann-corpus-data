/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the required header is
repeated verbatim as a module docstring immediately after the imports below.)
-/
import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

open scoped Polynomial

namespace Math2

attribute [local instance] FractionRing.liftAlgebra

set_option synthInstance.maxHeartbeats 400000 in
/--
**Resolution of singularities in characteristic zero, for curves (Hironaka; curve case).**

Setting: `k` is a field of characteristic zero and `A` is an integral domain which is
module-finite over a polynomial ring `k[X]` via an injective ring map.  By the Noether
normalization lemma this is exactly the algebraic description of (the coordinate ring of)
an integral affine curve over `k`: a finitely generated `k`-algebra domain of Krull
dimension one.  No smoothness whatsoever is assumed — `A` may be as singular as the
cuspidal ring `k[x,y]/(y² - x³)`.

Conclusion: the normalization `B = integralClosure A (Frac A)` of `A` inside its function
field resolves the singularities of `A`:

* `B` is a Dedekind domain;
* `B` has the *same* function field as `A` (`IsFractionRing B (Frac A)`), i.e. the induced
  morphism `Spec B → Spec A` is birational;
* `B` is a finite `A`-module, i.e. the morphism `Spec B → Spec A` is finite (in particular
  proper and surjective);
* every local ring of `B` at a nonzero prime is a discrete valuation ring, i.e. `Spec B` is
  a *regular* (nonsingular) curve.

Caveat on the formalization: this is the one-dimensional case of Hironaka's theorem, which
is the case that can be obtained by normalization; the statement proved here is not the
general higher-dimensional resolution theorem.
-/
theorem hironaka_resolution
    {k : Type*} [Field k] [CharZero k]
    {A : Type*} [CommRing A] [IsDomain A]
    [Algebra k[X] A] [Module.Finite k[X] A]
    (hinj : Function.Injective (algebraMap k[X] A)) :
    IsDedekindDomain (integralClosure A (FractionRing A)) ∧
    IsFractionRing (integralClosure A (FractionRing A)) (FractionRing A) ∧
    Module.Finite A (integralClosure A (FractionRing A)) ∧
    ∀ (P : Ideal (integralClosure A (FractionRing A))) [P.IsPrime], P ≠ ⊥ →
      IsDiscreteValuationRing (Localization.AtPrime P) := by
  haveI : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective ..).mpr hinj
  set K := FractionRing A with hK
  set C := integralClosure A K with hC
  -- `C` is also the integral closure of the polynomial subring `k[X]` in `K`.
  haveI hst : IsScalarTower k[X] ↥C K :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply k[X] A K]; rfl)
  haveI hic : IsIntegralClosure ↥C k[X] K := by
    constructor
    · exact Subtype.val_injective
    · intro x
      refine ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, ?_⟩
      rintro ⟨y, rfl⟩
      exact isIntegral_trans _ y.2
  -- `K` is a finite separable extension of `k(X) = Frac k[X]` (characteristic zero),
  -- and `k[X]` is a Dedekind domain, so the integral closure `C` is a Dedekind domain.
  haveI hdd : IsDedekindDomain ↥C :=
    IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X]) K ↥C
  haveI hfr : IsFractionRing ↥C K :=
    IsIntegralClosure.isFractionRing_of_finite_extension k[X] (FractionRing k[X]) K ↥C
  haveI hnoeth : IsNoetherian k[X] ↥C :=
    IsIntegralClosure.isNoetherian k[X] (FractionRing k[X]) K ↥C
  haveI : Module.Finite A ↥C := Module.Finite.of_restrictScalars_finite k[X] A ↥C
  refine ⟨hdd, hfr, inferInstance, ?_⟩
  intro P _ hP0
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥C hP0 _

end Math2

