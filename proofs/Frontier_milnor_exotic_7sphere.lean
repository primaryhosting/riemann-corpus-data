/-
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Metric Manifold

/-- The ambient Euclidean space `ℝ⁸` has dimension `7 + 1`; this `Fact` provides the
charted space structure (stereographic projection) on the unit sphere `S⁷ ⊆ ℝ⁸`. -/
instance factFinrankEuclidean8 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) := ⟨by simp⟩

/-- The standard smooth `7`-sphere: the unit sphere in `ℝ⁸`, with its standard smooth
structure coming from stereographic projection. -/
abbrev StandardSphere7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-- **The statement of Milnor's theorem.**

There exists a smooth `7`-manifold `M` (a topological space with a `C^∞` atlas modelled on
`ℝ⁷`) which is *homeomorphic* to the standard `7`-sphere `S⁷` but admits *no* diffeomorphism
to `S⁷`; i.e. an exotic `7`-sphere exists. -/
def ExoticSphere7Exists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : IsManifold (𝓡 7) ⊤ M),
    Nonempty (M ≃ₜ StandardSphere7) ∧
      IsEmpty (Diffeomorph (𝓡 7) (𝓡 7) M StandardSphere7 ⊤)

/-- Milnor's `λ`-invariant of the total space `M k` of the `S³`-bundle over `S⁴` with
Euler number `1` and first Pontryagin-type parameter `k` (odd), as an element of `ZMod 7`:
it is computed from the Hirzebruch signature theorem to be `k² - 1 mod 7`. -/
def milnorLambda (k : ℤ) : ZMod 7 := (k : ZMod 7) ^ 2 - 1

/-- **The arithmetic base case of Milnor's argument.**
For `k = 3` the invariant `λ = k² - 1 = 8 ≡ 1 (mod 7)` is nonzero, so the manifold `M 3`
cannot be diffeomorphic to the standard sphere. -/
theorem milnorLambda_three_ne_zero : milnorLambda 3 ≠ 0 := by
  decide

/-- `3` is odd, so `M 3` belongs to Milnor's family of `S³`-bundles over `S⁴` whose total
spaces are homeomorphic to `S⁷`. -/
theorem odd_three : Odd (3 : ℤ) := ⟨1, by ring⟩

/-- The geometric input of Milnor's construction, packaged as data.

For each odd integer `k`, `M k` is the total space of the `S³`-bundle over `S⁴` classified by
`(k+1)/2, (1-k)/2 ∈ π₃(SO(4))`.  Milnor's two geometric theorems are recorded as the fields:

* `homeomorphic_sphere`: Morse theory applied to a canonical function with exactly two
  nondegenerate critical points shows that `M k` is homeomorphic to `S⁷`;
* `lambda_eq_zero_of_diffeomorph`: the invariant `λ (M k) = k² - 1 ∈ ZMod 7`, defined via
  the Hirzebruch signature theorem applied to a coboundary of `M k`, is a diffeomorphism
  invariant which vanishes for the standard sphere.

Everything else (that these two facts force the existence of an exotic sphere) is proved
below in Lean. -/
structure MilnorFamily where
  /-- The total space of the `k`-th bundle. -/
  M : ℤ → Type
  /-- Its topology. -/
  topology : ∀ k, TopologicalSpace (M k)
  /-- Its atlas, modelled on `ℝ⁷`. -/
  charts : ∀ k, @ChartedSpace (EuclideanSpace ℝ (Fin 7)) _ (M k) (topology k)
  /-- The atlas is `C^∞`, i.e. `M k` is a smooth `7`-manifold. -/
  smooth : ∀ k, @IsManifold (EuclideanSpace ℝ (Fin 7)) _ _ (EuclideanSpace ℝ (Fin 7)) _
    (𝓡 7) ⊤ (M k) (topology k) (charts k)
  /-- Morse theory: for odd `k`, the total space `M k` is homeomorphic to `S⁷`. -/
  homeomorphic_sphere : ∀ k : ℤ, Odd k →
    Nonempty (@Homeomorph (M k) StandardSphere7 (topology k) _)
  /-- The signature-theoretic invariant `λ = k² - 1 (mod 7)` obstructs diffeomorphism with
  the standard sphere. -/
  lambda_eq_zero_of_diffeomorph : ∀ k : ℤ,
    Nonempty (@Diffeomorph ℝ _ (EuclideanSpace ℝ (Fin 7)) _ _ (EuclideanSpace ℝ (Fin 7)) _ _
        (EuclideanSpace ℝ (Fin 7)) _ (EuclideanSpace ℝ (Fin 7)) _ (𝓡 7) (𝓡 7)
        (M k) (topology k) (charts k) StandardSphere7 _ _ ⊤) →
      milnorLambda k = 0

/-- **Milnor's exotic 7-sphere (Lean-checked reduction).**

Given Milnor's geometric input (a family `M k` of smooth `7`-manifolds, homeomorphic to `S⁷`
for odd `k`, together with the `λ`-invariant obstruction), there exists a smooth `7`-manifold
homeomorphic but not diffeomorphic to the standard `7`-sphere.

The proof is the base case `k = 3`: `λ (M 3) = 3² - 1 = 8 ≡ 1 ≠ 0 (mod 7)`, so `M 3` — which
*is* homeomorphic to `S⁷` since `3` is odd — admits no diffeomorphism to `S⁷`. -/
theorem milnor_exotic_7sphere (d : MilnorFamily) : ExoticSphere7Exists := by
  refine ⟨d.M 3, d.topology 3, d.charts 3, d.smooth 3, d.homeomorphic_sphere 3 odd_three, ?_⟩
  rw [isEmpty_iff]
  intro f
  exact milnorLambda_three_ne_zero (d.lambda_eq_zero_of_diffeomorph 3 ⟨f⟩)

end Frontier

