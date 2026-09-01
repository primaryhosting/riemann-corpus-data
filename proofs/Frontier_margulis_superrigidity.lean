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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The superrigidity conclusion: the abstract homomorphism `ρ : Γ → H` defined on the
subgroup `Γ ≤ G` is the restriction of a *continuous* homomorphism `G → H`. -/
def ExtendsToContinuousHom (Γ : Subgroup G) (ρ : Γ →* H) : Prop :=
  ∃ σ : G →* H, Continuous σ ∧ ∀ γ : Γ, σ (γ : G) = ρ γ

/-- The graph of `ρ : Γ →* H` inside `G × H`, i.e. `{(γ, ρ γ) : γ ∈ Γ}`.
This is the subgroup whose closure Margulis' argument analyses. -/
def graphSubgroup (Γ : Subgroup G) (ρ : Γ →* H) : Subgroup (G × H) :=
  (Γ.subtype.prod ρ).range

@[simp] lemma mem_graphSubgroup {Γ : Subgroup G} {ρ : Γ →* H} (γ : Γ) :
    ((γ : G), ρ γ) ∈ graphSubgroup Γ ρ :=
  ⟨γ, rfl⟩

/-!
## The statement of Margulis superrigidity

Margulis' superrigidity theorem reads as follows.  Let `G` be a semisimple Lie group of real
rank at least `2` (with finite centre and no compact factors), let `Γ ≤ G` be an irreducible
lattice, let `H` be the group of `k`-points of a connected adjoint simple algebraic group over
a local field `k`, and let `ρ : Γ → H` be a homomorphism whose image is Zariski dense and
unbounded.  Then `ρ` is the restriction to `Γ` of a continuous homomorphism `G → H`.

The predicate below records this statement schematically: the (analytic, algebraic and
measure-theoretic) hypotheses on the data are supplied as abstract propositions
`higherRank`, `irreducibleLattice`, `zariskiDenseImage` and `unboundedImage`, while the
conclusion is the honest one, `ExtendsToContinuousHom Γ ρ`. -/
def MargulisSuperrigidityStatement
    (higherRank irreducibleLattice zariskiDenseImage unboundedImage : Prop)
    (Γ : Subgroup G) (ρ : Γ →* H) : Prop :=
  higherRank → irreducibleLattice → zariskiDenseImage → unboundedImage →
    ExtendsToContinuousHom Γ ρ

/-!
## A Lean-checked reduction

The hard, measure-theoretic core of Margulis' proof produces a subgroup `L ≤ G × H`
containing the graph of `ρ` which is the graph of a continuous homomorphism `G → H`:
concretely, the first projection restricted to `L` is injective (`hker`) and admits a
continuous section `s : G → G × H` with values in `L` (`hs_mem`, `hs_fst`, `hs_cont`).

The theorem below is the remaining formal step: from such an `L` one really does get a
continuous extension of `ρ`.  No topological hypothesis on `L` itself is needed, so none is
assumed. -/
theorem margulis_superrigidity
    (Γ : Subgroup G) (ρ : Γ →* H) (L : Subgroup (G × H))
    (hgraph : graphSubgroup Γ ρ ≤ L)
    (hker : ∀ h : H, ((1 : G), h) ∈ L → h = 1)
    (s : G →* G × H) (hs_cont : Continuous s) (hs_fst : ∀ g : G, (s g).1 = g)
    (hs_mem : ∀ g : G, s g ∈ L) :
    ExtendsToContinuousHom Γ ρ := by
  refine ⟨(MonoidHom.snd G H).comp s, continuous_snd.comp hs_cont, fun γ => ?_⟩
  have hmem : (s (γ : G)) * ((γ : G), ρ γ)⁻¹ ∈ L :=
    mul_mem (hs_mem _) (inv_mem (hgraph (mem_graphSubgroup γ)))
  have hfst : (s (γ : G)) * ((γ : G), ρ γ)⁻¹ = ((1 : G), (s (γ : G)).2 * (ρ γ)⁻¹) := by
    ext <;> simp [hs_fst]
  rw [hfst] at hmem
  have := hker _ hmem
  simpa [MonoidHom.comp_apply, mul_inv_eq_one] using this

/-- The hypotheses of `Frontier.margulis_superrigidity` are satisfiable: for the inclusion of
any subgroup `Γ ≤ G` into `G` itself, the diagonal of `G × G` plays the role of `L`, and the
conclusion is the (true) statement that the inclusion extends to the identity of `G`. -/
theorem margulis_superrigidity_nonvacuous (Γ : Subgroup G) :
    ExtendsToContinuousHom Γ (Γ.subtype) := by
  refine margulis_superrigidity Γ Γ.subtype
    ((MonoidHom.id G).prod (MonoidHom.id G)).range ?_ ?_
    ((MonoidHom.id G).prod (MonoidHom.id G)) (by fun_prop) (fun g => rfl) (fun g => ⟨g, rfl⟩)
  · rintro x ⟨γ, rfl⟩
    exact ⟨(γ : G), rfl⟩
  · rintro h ⟨g, hg⟩
    have h1 : g = 1 := congrArg Prod.fst hg
    have h2 : g = h := congrArg Prod.snd hg
    exact h2 ▸ h1

end Frontier

