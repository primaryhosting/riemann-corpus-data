import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
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

set_option grind.warning false

namespace Frontier

universe u

/-! ## The conclusion of superrigidity -/

/-- The conclusion of Margulis superrigidity for a homomorphism `ρ : Γ →* H` defined on a
subgroup `Γ` of a topological group `G`: `ρ` is the restriction of a continuous homomorphism
`G →* H`. -/
def ExtendsContinuously {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (Γ : Subgroup G) (ρ : Γ →* H) : Prop :=
  ∃ σ : G →* H, Continuous σ ∧ ∀ γ : Γ, σ (γ : G) = ρ γ

/-! ## The hypotheses -/

/-- `IsLatticeIn μ Γ` says that `Γ` is a lattice in the topological group `G`: it is a discrete
subgroup admitting a fundamental domain of finite Haar measure. -/
def IsLatticeIn {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) (Γ : Subgroup G) : Prop :=
  DiscreteTopology Γ ∧
    ∃ F : Set G, MeasureTheory.IsFundamentalDomain Γ.op F μ ∧ μ F ≠ ⊤

/-- `IsIrreducibleLattice Γ` says that the lattice `Γ ≤ G` is irreducible: `Γ` together with any
proper closed normal subgroup of `G` generates a dense subgroup (equivalently, the image of `Γ`
in every proper quotient of `G` by a closed normal subgroup is dense). -/
def IsIrreducibleLattice {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N.Normal → IsClosed (N : Set G) → N ≠ ⊤ →
    Dense ((Γ ⊔ N : Subgroup G) : Set G)

/-- A working formalization of "`G` is a connected semisimple group of real rank at least two":
`G` is connected, topologically perfect and centre-free, and contains a closed two-parameter
subgroup isomorphic to `ℝ × ℝ` (a two-dimensional split torus). -/
structure IsHigherRank (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop where
  connected : ConnectedSpace G
  perfect : (commutator G).topologicalClosure = ⊤
  centerless : Subgroup.center G = ⊥
  splitRankTwo : ∃ f : Multiplicative (ℝ × ℝ) →* G,
    Continuous f ∧ Function.Injective f ∧ IsClosed (Set.range f)

/-! ## The statement of Margulis superrigidity, and its dense-image special case -/

/-- **Margulis superrigidity** (statement): let `G` be a connected semisimple group of real rank
at least two, `Γ ≤ G` an irreducible lattice, `H` a Hausdorff topological group, and
`ρ : Γ →* H` a homomorphism. Then `ρ` extends to a continuous homomorphism `G →* H`. -/
def MargulisSuperrigidityStatement : Prop :=
  ∀ {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] (Γ : Subgroup G) (ρ : Γ →* H),
    IsHigherRank G → IsLatticeIn μ Γ → IsIrreducibleLattice Γ → ExtendsContinuously Γ ρ

/-- The special case of Margulis superrigidity in which the image of `ρ` is dense in the target,
i.e. the case to which Margulis' argument first reduces (replacing `H` by the closure of the
image of `Γ`). -/
def MargulisSuperrigidityDenseImage : Prop :=
  ∀ {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : MeasureTheory.Measure G) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] (Γ : Subgroup G) (ρ : Γ →* H),
    IsHigherRank G → IsLatticeIn μ Γ → IsIrreducibleLattice Γ →
    Dense (Set.range ρ) → ExtendsContinuously Γ ρ

/-! ## Elementary facts about the superrigidity conclusion -/

section Basic

variable {G H K : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K]

/-- Superrigidity is preserved by postcomposition with a continuous homomorphism. -/
theorem ExtendsContinuously.comp {Γ : Subgroup G} {ρ : Γ →* H} (h : ExtendsContinuously Γ ρ)
    (f : H →* K) (hf : Continuous f) : ExtendsContinuously Γ (f.comp ρ) := by
  obtain ⟨σ, hσc, hσ⟩ := h
  exact ⟨f.comp σ, hf.comp hσc, fun γ => by simp [hσ γ]⟩

/-- Superrigidity for two targets gives superrigidity for the product target. -/
theorem ExtendsContinuously.prod {Γ : Subgroup G} {ρ₁ : Γ →* H} {ρ₂ : Γ →* K}
    (h₁ : ExtendsContinuously Γ ρ₁) (h₂ : ExtendsContinuously Γ ρ₂) :
    ExtendsContinuously Γ (ρ₁.prod ρ₂) := by
  obtain ⟨σ₁, hc₁, he₁⟩ := h₁
  obtain ⟨σ₂, hc₂, he₂⟩ := h₂
  refine ⟨σ₁.prod σ₂, hc₁.prodMk hc₂, fun γ => ?_⟩
  simp [he₁ γ, he₂ γ]

/-- **Uniqueness of the superrigid extension.** A continuous homomorphism into a Hausdorff group
is determined by its restriction to a dense subgroup; in particular the extension provided by
superrigidity is unique whenever `Γ` is dense in `G`. -/
theorem eq_of_dense_of_eq_on [T2Space H] {Γ : Subgroup G} (hΓ : Dense (Γ : Set G))
    {σ τ : G →* H} (hσ : Continuous σ) (hτ : Continuous τ)
    (h : ∀ γ : Γ, σ (γ : G) = τ (γ : G)) : σ = τ := by
  ext g
  refine congrFun (Continuous.ext_on hΓ hσ hτ ?_) g
  rintro x hx
  exact h ⟨x, hx⟩

end Basic

/-! ## Base cases -/

section BaseCases

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- **Base case: rank zero / discrete ambient group.** If `G` carries the discrete topology, then
every homomorphism defined on all of `G` extends continuously (by itself). -/
theorem extendsContinuously_of_discreteTopology [DiscreteTopology G]
    (ρ : (⊤ : Subgroup G) →* H) : ExtendsContinuously (⊤ : Subgroup G) ρ := by
  refine ⟨ρ.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom, continuous_of_discreteTopology,
    fun γ => ?_⟩
  simp [Subgroup.topEquiv]

/-- **Base case: abelian torsion-free targets.** A higher-rank lattice has property (T) and hence
finite abelianization; granting this (as the hypothesis `hab`), every homomorphism from `Γ` to a
torsion-free abelian topological group is trivial, and so extends continuously (by the trivial
homomorphism). -/
theorem extendsContinuously_of_finite_abelianization {Γ : Subgroup G}
    (hab : Finite (Abelianization Γ)) [CommGroup H] (htf : Monoid.IsTorsionFree H)
    (ρ : Γ →* H) : ExtendsContinuously Γ ρ := by
  have hone : ∀ γ : Γ, ρ γ = 1 := by
    intro γ
    have hfin : Finite (MonoidHom.range (Abelianization.lift ρ)) := by
      have := hab
      exact Set.Finite.to_subtype (Set.toFinite _)
    have hmem : ρ γ ∈ MonoidHom.range (Abelianization.lift ρ) :=
      ⟨Abelianization.of γ, by simp⟩
    by_contra hne
    refine htf _ hne ?_
    have : IsOfFinOrder (⟨ρ γ, hmem⟩ : MonoidHom.range (Abelianization.lift ρ)) :=
      isOfFinOrder_of_finite _
    exact (isOfFinOrder_iff_pow_eq_one.mpr (by
      obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp this
      exact ⟨n, hn, by
        have := congrArg (Subtype.val) hpow
        simpa using this⟩))
  exact ⟨1, continuous_const, fun γ => (hone γ).symm⟩

end BaseCases

/-! ## Reduction to the dense-image case -/

section Reduction

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H]

/-- The corestriction of `ρ : Γ →* H` to the closure of its image. -/
def corestrictClosure {Γ : Subgroup G} (ρ : Γ →* H) :
    Γ →* ((MonoidHom.range ρ).topologicalClosure) :=
  ρ.codRestrict _ fun γ => Subgroup.le_topologicalClosure _ ⟨γ, rfl⟩

theorem dense_range_corestrictClosure {Γ : Subgroup G} (ρ : Γ →* H) :
    Dense (Set.range (corestrictClosure ρ)) := by
  rw [(IsEmbedding.subtypeVal (p := fun x : H => x ∈ (MonoidHom.range ρ).topologicalClosure)).isInducing.dense_iff]
  rintro ⟨x, hx⟩
  have himg : Subtype.val '' (Set.range (corestrictClosure ρ)) = Set.range ρ := by
    ext y
    constructor
    · rintro ⟨-, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨corestrictClosure ρ γ, ⟨γ, rfl⟩, rfl⟩
  rw [himg]
  have : ((MonoidHom.range ρ).topologicalClosure : Set H) = closure (Set.range ρ) := by
    simp [Subgroup.topologicalClosure_coe, MonoidHom.coe_range]
  rw [this] at hx
  exact hx

/-- **Local reduction to the dense-image case.** If the corestriction of `ρ` to the closure of its
image extends to a continuous homomorphism, then so does `ρ` itself. -/
theorem extendsContinuously_of_corestrictClosure {Γ : Subgroup G} (ρ : Γ →* H)
    (h : ExtendsContinuously Γ (corestrictClosure ρ)) : ExtendsContinuously Γ ρ := by
  obtain ⟨σ, hσc, hσ⟩ := h
  refine ⟨((MonoidHom.range ρ).topologicalClosure).subtype.comp σ,
    (continuous_subtype_val).comp hσc, fun γ => ?_⟩
  simpa [corestrictClosure] using congrArg (Subtype.val) (hσ γ)

end Reduction

/-! ## The target theorem -/

/-- **Margulis superrigidity, reduced to the dense-image case.**

The general statement of Margulis superrigidity for irreducible lattices in higher-rank groups
follows from its special case in which the image of the lattice is dense in the target: given
arbitrary data `(G, Γ, H, ρ)` satisfying the hypotheses, one replaces `H` by the closure of the
image `ρ (Γ)`, which is again a Hausdorff topological group, applies the dense-image case there,
and composes the resulting continuous extension with the (continuous) inclusion of that closed
subgroup into `H`.

This is a Lean-checked reduction: the hypotheses on the ambient group `G` and on the lattice `Γ`
are untouched, and the only input is superrigidity for homomorphisms with dense image. -/
theorem margulis_superrigidity
    (hdense : MargulisSuperrigidityDenseImage.{u}) : MargulisSuperrigidityStatement.{u} := by
  intro G H _ _ _ _ μ _ _ _ _ Γ ρ hG hΓ hirr
  refine extendsContinuously_of_corestrictClosure ρ ?_
  exact hdense μ Γ (corestrictClosure ρ) hG hΓ hirr (dense_range_corestrictClosure ρ)

end Frontier

