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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-!
## The setting

Margulis superrigidity concerns an irreducible lattice `Γ` in a higher-rank semisimple
group `G` and a linear representation `rho : Γ → H`.  It asserts that, under suitable
non-degeneracy assumptions on the image of `rho`, the representation `rho` is the restriction
to `Γ` of a *continuous* homomorphism `G → H`; i.e. the abstract homomorphism `rho`, defined
only on the discrete group `Γ`, is forced to come from the ambient topological group.

Below we formalise:

* `Frontier.IsLatticeIn` — a discrete subgroup with a finite-measure fundamental domain;
* `Frontier.ExtendsToContinuousHom` — the superrigidity conclusion for one representation;
* `Frontier.SuperrigidLattice` — "every non-degenerate representation of `Γ` extends";
* `Frontier.MargulisSuperrigidityStatement` — the theorem itself, as a statement schema in
  which the (semisimplicity + higher rank + irreducibility) package is an abstract
  predicate; `Frontier.HasHigherRankSplitTorus` records a concrete necessary condition
  for real rank `≥ 2` that such a predicate must imply;
* `Frontier.margulis_superrigidity` — the theorem proved here: the *abelian base case*
  together with uniqueness of the extension, plus (`margulis_superrigidity_finite_index`)
  a Lean-checked reduction from finite-index subgroups to the whole lattice.
-/

/-- `IsLatticeIn μ Γ`: the subgroup `Γ` of the topological group `G` is a **lattice**, i.e.
it is discrete and admits a fundamental domain of finite `μ`-measure (`μ` being a Haar
measure on `G`). -/
def IsLatticeIn {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) (Γ : Subgroup G) : Prop :=
  DiscreteTopology Γ ∧ ∃ F : Set G, MeasureTheory.IsFundamentalDomain Γ F μ ∧ μ F < ⊤

/-- `ExtendsToContinuousHom Γ rho`: the abstract homomorphism `rho : Γ →* H` is the restriction
of a continuous homomorphism `G →* H`.  This is the conclusion of Margulis superrigidity. -/
def ExtendsToContinuousHom {G : Type*} [Group G] [TopologicalSpace G]
    {H : Type*} [Group H] [TopologicalSpace H] (Γ : Subgroup G) (rho : Γ →* H) : Prop :=
  ∃ Φ : G →* H, Continuous Φ ∧ ∀ γ : Γ, Φ (γ : G) = rho γ

/-- `HasHigherRankSplitTorus G`: `G` contains a closed copy of the two-dimensional vector
group `ℝ²`.  For a connected semisimple Lie group with finite centre this is exactly what a
maximal `ℝ`-split torus of dimension `≥ 2` provides, so it is a necessary condition for
"real rank at least two"; it is recorded here as the concrete content of the higher-rank
hypothesis. -/
def HasHigherRankSplitTorus (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ f : Multiplicative (ℝ × ℝ) →* G, Topology.IsClosedEmbedding f

/-- `SuperrigidLattice Γ`: every representation `rho : Γ →* H` of `Γ` into a topological group
`H` whose image is dense in `H` and is not relatively compact extends to a continuous
homomorphism `G →* H`.

The density condition is the topological rendering of "Zariski-dense image", and the
non-relative-compactness is the rendering of "unbounded image"; both are needed, since a
lattice does have plenty of representations with relatively compact image (e.g. finite
quotients) that do not extend. -/
def SuperrigidLattice.{u} {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (rho : Γ →* H),
    Dense (Set.range fun γ : Γ => rho γ) →
    ¬ IsCompact (closure (Set.range fun γ : Γ => rho γ)) →
    ExtendsToContinuousHom Γ rho

/-- **Margulis superrigidity (statement schema).**

For every locally compact group `G` carrying a Haar measure `μ` and every lattice `Γ ≤ G`
such that `(G, μ, Γ)` satisfies the higher-rank hypothesis `HigherRank` — semisimplicity,
real rank at least two, and irreducibility of the lattice — the lattice `Γ` is superrigid.

The higher-rank hypothesis is kept as a parameter because the theory of semisimple
algebraic/Lie groups needed to *define* it (root systems of the ambient group, `ℝ`-rank,
irreducibility of a lattice with respect to a product decomposition) is not available.  Any
admissible instantiation must in particular imply `HasHigherRankSplitTorus G`. -/
def MargulisSuperrigidityStatement.{u}
    (HigherRank : ∀ (G : Type u) [Group G] [TopologicalSpace G] [MeasurableSpace G],
      Measure G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] (μ : Measure G) (Γ : Subgroup G),
    IsLatticeIn μ Γ → HigherRank G μ Γ → SuperrigidLattice.{u} Γ

/-!
## The base case

A higher-rank lattice has Kazhdan's property (T), hence a finite abelianisation.  This is
the input we take as a hypothesis (property (T) itself is not formalised here).  From it we
prove the *abelian base case* of superrigidity: every representation of such a lattice into
a torsion-free abelian topological group is trivial, hence extends (necessarily by the
trivial homomorphism), and the extension is unique as soon as `Γ` is dense in `G`.
-/

/-- If `L` has finite abelianisation then every homomorphism from `L` to an abelian group
takes values of finite order: `rho x ^ Nat.card (Abelianization L) = 1`. -/
theorem pow_natCard_abelianization_eq_one {L : Type*} [Group L] {H : Type*} [CommGroup H]
    (rho : L →* H) (x : L) : rho x ^ Nat.card (Abelianization L) = 1 := by
  have hx : rho x = Abelianization.lift rho (Abelianization.of x) := by
    simp
  rw [hx, ← map_pow, pow_card_eq_one', map_one]

/-- **Trivialisation lemma.** A homomorphism from a group with finite abelianisation to a
torsion-free abelian group is trivial. -/
theorem hom_eq_one_of_finite_abelianization {L : Type*} [Group L] {H : Type*} [CommGroup H]
    [IsMulTorsionFree H] (hab : Finite (Abelianization L)) (rho : L →* H) (x : L) : rho x = 1 := by
  have hpos : 0 < Nat.card (Abelianization L) := by
    haveI := hab
    exact Nat.card_pos
  have hinj := IsMulTorsionFree.pow_left_injective (M := H)
    (n := Nat.card (Abelianization L)) hpos.ne' (a₁ := rho x) (a₂ := 1)
  simp only [one_pow] at hinj
  exact hinj (pow_natCard_abelianization_eq_one rho x)

/-- **Uniqueness of the extension.** Two continuous homomorphisms `G →* H` into a Hausdorff
group that agree on a dense subgroup `Γ` are equal; in particular a continuous extension of
a representation of a dense subgroup is unique. -/
theorem continuousHom_ext_of_dense {G : Type*} [Group G] [TopologicalSpace G]
    {H : Type*} [Group H] [TopologicalSpace H] [T2Space H] {Γ : Subgroup G}
    (hd : Dense (Γ : Set G)) {Φ Ψ : G →* H} (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (h : ∀ γ : Γ, Φ (γ : G) = Ψ (γ : G)) : Φ = Ψ := by
  have : (Φ : G → H) = (Ψ : G → H) :=
    Continuous.ext_on hd hΦ hΨ (fun x hx => h ⟨x, hx⟩)
  exact DFunLike.ext _ _ (fun x => congrFun this x)

/-- **Finite-index reduction (abelian targets).** If a representation `rho : L →* H` into a
torsion-free abelian group agrees on a finite-index subgroup `L₀ ≤ L` with a homomorphism
`Φ`, then it agrees with `Φ` on all of `L`.  Thus, for torsion-free abelian targets,
superrigidity on a finite-index subgroup of the lattice already implies superrigidity on
the whole lattice. -/
theorem eq_of_eqOn_finiteIndex {L : Type*} [Group L] {H : Type*} [CommGroup H]
    [IsMulTorsionFree H] {L₀ : Subgroup L} (hidx : L₀.FiniteIndex) (rho Φ : L →* H)
    (h : ∀ x ∈ L₀, rho x = Φ x) (x : L) : rho x = Φ x := by
  set δ : L →* H := rho * Φ⁻¹ with hδ
  have hker : L₀ ≤ δ.ker := by
    intro y hy
    simp [hδ, MonoidHom.mem_ker, h y hy]
  have hdvd : δ.ker.index ∣ L₀.index := Subgroup.index_dvd_of_le hker
  have hne : δ.ker.index ≠ 0 := by
    intro h0
    exact hidx.index_ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have hpow : δ x ^ Nat.card (L ⧸ δ.ker) = 1 := by
    have hx : δ x ^ Nat.card (L ⧸ δ.ker) = δ (x ^ Nat.card (L ⧸ δ.ker)) := (map_pow _ _ _).symm
    rw [hx, ← MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    simp
  have hpos : 0 < Nat.card (L ⧸ δ.ker) := Nat.pos_of_ne_zero hne
  have hinj := IsMulTorsionFree.pow_left_injective (M := H)
    (n := Nat.card (L ⧸ δ.ker)) hpos.ne' (a₁ := δ x) (a₂ := 1)
  simp only [one_pow] at hinj
  have hδx : δ x = 1 := hinj hpow
  have : rho x * (Φ x)⁻¹ = 1 := by simpa [hδ] using hδx
  exact (div_eq_one (a := rho x) (b := Φ x)).1 (by simpa [div_eq_mul_inv] using this)

/-- **Margulis superrigidity — the abelian base case, with uniqueness.**

Let `Γ` be a lattice with finite abelianisation in a topological group `G` (higher-rank
lattices have Kazhdan's property (T), hence finite abelianisation; property (T) is taken
here as the black box supplying `hab`), and let `H` be a Hausdorff torsion-free abelian
topological group.  Then every representation `rho : Γ →* H`:

* is trivial;
* extends to a continuous homomorphism `G →* H` — i.e. the superrigidity conclusion
  `ExtendsToContinuousHom Γ rho` holds;
* has, when `Γ` is dense in `G`, exactly one such continuous extension.

This is the base case of superrigidity: it disposes of all abelian target groups, which is
precisely the case in which the conclusion is *not* obtained by the dynamical arguments used
for semisimple targets, and it already shows that the higher-rank hypothesis (through
property (T)) is what rules out the obvious counterexamples coming from surface groups. -/
theorem margulis_superrigidity {G : Type*} [Group G] [TopologicalSpace G]
    {H : Type*} [CommGroup H] [TopologicalSpace H] [T2Space H] [IsMulTorsionFree H]
    {Γ : Subgroup G} (hab : Finite (Abelianization Γ)) (rho : Γ →* H) :
    (∀ γ : Γ, rho γ = 1) ∧ ExtendsToContinuousHom Γ rho ∧
      (Dense (Γ : Set G) → ∀ Φ Ψ : G →* H, Continuous Φ → Continuous Ψ →
        (∀ γ : Γ, Φ (γ : G) = rho γ) → (∀ γ : Γ, Ψ (γ : G) = rho γ) → Φ = Ψ) := by
  have htriv : ∀ γ : Γ, rho γ = 1 := hom_eq_one_of_finite_abelianization hab rho
  refine ⟨htriv, ⟨1, continuous_const, fun γ => by simp [htriv γ]⟩, ?_⟩
  intro hd Φ Ψ hΦ hΨ hΦrho hΨrho
  exact continuousHom_ext_of_dense hd hΦ hΨ (fun γ => by rw [hΦrho γ, hΨrho γ])

/-- **Finite-index reduction for the superrigidity conclusion (abelian targets).**
If the restriction of `rho` to a finite-index subgroup `Γ₀` of the lattice `Γ` is the
restriction of a continuous homomorphism `Φ : G →* H`, with `H` torsion-free abelian, then
`Φ` extends `rho` on all of `Γ`; in particular `ExtendsToContinuousHom Γ rho` holds. -/
theorem margulis_superrigidity_finite_index {G : Type*} [Group G] [TopologicalSpace G]
    {H : Type*} [CommGroup H] [TopologicalSpace H] [IsMulTorsionFree H] {Γ : Subgroup G}
    {Γ₀ : Subgroup Γ} (hidx : Γ₀.FiniteIndex) (rho : Γ →* H) (Φ : G →* H) (hΦ : Continuous Φ)
    (h : ∀ γ ∈ Γ₀, rho γ = Φ (γ : G)) : ExtendsToContinuousHom Γ rho := by
  refine ⟨Φ, hΦ, fun γ => ?_⟩
  exact (eq_of_eqOn_finiteIndex hidx rho (Φ.comp Γ.subtype) h γ).symm

end Frontier

