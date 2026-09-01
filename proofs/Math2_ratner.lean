import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
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

namespace Math2

open MeasureTheory

/-!
## Ratner's orbit-closure theorem for one-parameter (unipotent) flows

Setting: a topological abelian group `G` (written additively), a subgroup `Γ ≤ G`, the
homogeneous space `G ⧸ Γ`, and a one-parameter subgroup `u : ℝ →+ G` acting on `G ⧸ Γ` by
translation, `t • (x Γ) = (x + u t) Γ`.  In an abelian group every one-parameter subgroup is
unipotent, so this is exactly the setting of Ratner's orbit-closure theorem in the commutative
case (the classical Kronecker picture: on `ℝⁿ / ℤⁿ` the closure of a linear orbit is a coset of
a closed subgroup).

`Math2.ratner` states the conclusion of the orbit-closure theorem: the closure of the orbit of
any point is a *coset of a closed subgroup* `H` of `G ⧸ Γ`, where `H` contains the flow and is
the smallest closed subgroup that does so; in particular the orbit closure is homogeneous, i.e.
invariant under the flow.
-/

/-- **Ratner's orbit-closure theorem (commutative case).**

Let `G` be a topological abelian group, `Γ ≤ G` a subgroup and `u : ℝ →+ G` a one-parameter
subgroup, acting on the homogeneous space `G ⧸ Γ` by `t ↦ (· + u t)`.  Then for every `x : G`
there is a *closed subgroup* `H ≤ G ⧸ Γ` such that

* `H` contains the image of the flow;
* `H` is the smallest closed subgroup with that property;
* the closure of the orbit of `x Γ` is the coset `x Γ + H`;
* consequently the orbit closure is invariant under the flow.

Thus every orbit closure of the flow is homogeneous: a coset of a closed subgroup.  (No
continuity assumption on `u` is needed for this conclusion.) -/
theorem ratner {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (Γ : AddSubgroup G) (u : ℝ →+ G) (x : G) :
    ∃ H : AddSubgroup (G ⧸ Γ),
      IsClosed (H : Set (G ⧸ Γ)) ∧
      (∀ t : ℝ, ((u t : G) : G ⧸ Γ) ∈ H) ∧
      (∀ K : AddSubgroup (G ⧸ Γ), IsClosed (K : Set (G ⧸ Γ)) →
        (∀ t : ℝ, ((u t : G) : G ⧸ Γ) ∈ K) → H ≤ K) ∧
      closure (Set.range fun t : ℝ => ((x + u t : G) : G ⧸ Γ))
          = ((x : G) : G ⧸ Γ) +ᵥ (H : Set (G ⧸ Γ)) ∧
      (∀ t : ℝ, ((u t : G) : G ⧸ Γ) +ᵥ
          closure (Set.range fun s : ℝ => ((x + u s : G) : G ⧸ Γ))
        = closure (Set.range fun s : ℝ => ((x + u s : G) : G ⧸ Γ))) := by
  set f : ℝ →+ (G ⧸ Γ) := (QuotientAddGroup.mk' Γ).comp u with hf
  set H : AddSubgroup (G ⧸ Γ) := (AddMonoidHom.range f).topologicalClosure with hH
  have hmem : ∀ t : ℝ, ((u t : G) : G ⧸ Γ) ∈ H := fun t =>
    AddSubgroup.le_topologicalClosure _ ⟨t, rfl⟩
  have horb : closure (Set.range fun t : ℝ => ((x + u t : G) : G ⧸ Γ))
      = ((x : G) : G ⧸ Γ) +ᵥ (H : Set (G ⧸ Γ)) := by
    have h1 : (Set.range fun t : ℝ => ((x + u t : G) : G ⧸ Γ))
        = ((x : G) : G ⧸ Γ) +ᵥ (Set.range fun t : ℝ => f t) := by
      ext y
      simp [hf, Set.mem_vadd_set, eq_comm]
    rw [h1, closure_vadd, hH, AddSubgroup.topologicalClosure_coe, AddMonoidHom.coe_range]
  refine ⟨H, AddSubgroup.isClosed_topologicalClosure _, hmem, ?_, horb, ?_⟩
  · intro K hK hKmem
    refine AddSubgroup.topologicalClosure_minimal _ ?_ hK
    rintro y ⟨t, rfl⟩
    exact hKmem t
  · intro t
    rw [horb]
    ext y
    constructor
    · rintro ⟨z, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨((u t : G) : G ⧸ Γ) + h, H.add_mem (hmem t) hh, by
        simp only [vadd_eq_add]; abel⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨((x : G) : G ⧸ Γ) + (-((u t : G) : G ⧸ Γ) + h), ⟨-((u t : G) : G ⧸ Γ) + h,
        H.add_mem (H.neg_mem (hmem t)) hh, rfl⟩, ?_⟩
      simp [vadd_eq_add]
      abel

/-!
## Ratner's measure-classification theorem for a unipotent flow on the circle

For the one-parameter flow `t ↦ x + t·α` on the circle `AddCircle T` with `α ≠ 0`, the only
invariant Borel probability measure is the homogeneous (Haar) one.  This is the conclusion of
Ratner's measure-classification theorem in this baby case: every invariant probability measure
is the Haar measure of a closed subgroup coset — here the whole circle.
-/

/-- **Ratner's measure-classification theorem for the linear flow on a circle.**

If `α ≠ 0` and `μ` is a Borel probability measure on `AddCircle T` invariant under every
time-`t` map `y ↦ (t·α) + y` of the flow, then `μ` is the Haar probability measure. -/
theorem ratner_measure_circle {T : ℝ} [Fact (0 < T)] (α : ℝ) (hα : α ≠ 0)
    (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (fun y : AddCircle T => ((t * α : ℝ) : AddCircle T) + y) μ = μ) :
    μ = AddCircle.haarAddCircle := by
  haveI : μ.IsAddLeftInvariant := by
    constructor
    intro g
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples T) g
    have h := hinv (r / α)
    rwa [div_mul_cancel₀ _ hα] at h
  haveI : μ.IsAddHaarMeasure := by constructor
  exact MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure μ _

end Math2

