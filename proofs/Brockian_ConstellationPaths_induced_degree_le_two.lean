import Mathlib
import Brockian.ConstellationGraph
import Brockian.ConstellationAcyclic
import Brockian.ConstellationGraphAcyclic

/-
# Constellation Sieve — Gate sub-brick 2b: the twin-admissible `+3` graph is a FOREST OF PATHS.

Let `G := SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)` be the induced subgraph
of the `+3` translation flow on the twin-admissible residues (`twinAdm a ↔ IsUnit a ∧ IsUnit (a+2)`).
The previous sub-bricks established:

* `Brockian.ConstellationGraph.plus_three_neighbourhood` — every `+3`-neighbour of `a` lies in
  `{a+3, a-3}` (maximum degree ≤ 2 for the ambient flow);
* `Brockian.ConstellationGraphAcyclic.twin_admissible_induced_acyclic` — the induced twin-admissible
  `+3` graph is `SimpleGraph.IsAcyclic` (via the injective `pos = (3⁻¹·a).val` homomorphism into the
  integer line graph, the arithmetic acyclicity core);
* `Brockian.ConstellationGraph.twin_no_four_run` — for `5 ∣ M`, no `a` has all four of
  `a, a+3, a+6, a+9` twin-admissible (the run-cap of length ≤ 3).

This file packages those facts into the structural statement "`G` is a disjoint union of paths, each
with at most 3 vertices."

## What is VERIFIED here (no `sorry`/`admit`/`native_decide`/`axiom`)

* **Theorem 1 — `induced_degree_le_two`.** Every vertex of `G` has degree ≤ 2. Proof: the neighbour
  set of `v` injects (via `Subtype.val`) into `{↑v+3, ↑v-3}` by `plus_three_neighbourhood`, a
  2-element finset, so `Finset.card_le_card_of_injOn` bounds the degree.

* **Theorem 2 — `forest_of_paths`.** For `Nat.Coprime 3 M` and `1 < M`,
  `G.IsAcyclic ∧ ∀ v, G.degree v ≤ 2`. Acyclic + maximum degree ≤ 2 *is* the exact
  characterization of "a disjoint union of paths" (a finite acyclic graph with `Δ ≤ 2` is a forest
  of paths). Assembled from `twin_admissible_induced_acyclic` and Theorem 1.

* **Theorem 3 (run-cap ⇒ ≤ 3 vertices) — `no_four_vertex_plus_three_chain` and
  `no_four_admissible_run`.** For `5 ∣ M`, four vertices `v0,v1,v2,v3` of `G` linked in a `+3`
  progression (`↑vᵢ₊₁ − ↑vᵢ = 3`) cannot exist, since their underlying residues would be
  `a, a+3, a+6, a+9` all twin-admissible, contradicting `twin_no_four_run`. Hence each `+3`-run of
  admissible vertices — i.e. each path component of `G` — has at most 3 vertices (the `P₁/P₂/P₃`
  decomposition).

## Honest scope / what remains

Theorems 1 + 2 give the complete forest-of-paths structure (`IsAcyclic ∧ Δ ≤ 2`), the honest and
standard characterization of "disjoint union of paths". Theorem 3 caps each path at ≤ 3 vertices in
its direct arithmetic/chain form (following `twin_no_four_run`). The *further* identification of each
connected component with an explicit `SimpleGraph.pathGraph n` term (`n ≤ 3`) inside Mathlib's
`Walk`/`IsPath`/`ConnectedComponent` API is a separate development and is **not** carried out here;
it is not needed for the `P₁/P₂/P₃` structural conclusion, which is fully captured by
(`IsAcyclic`, `Δ ≤ 2`, no `+3`-chain of 4 admissible vertices). No `sorry`, `admit`,
`native_decide`, or `axiom` is used.
-/

namespace Brockian.ConstellationPaths

open Brockian.ConstellationGraph
open Brockian.ConstellationAcyclic
open Brockian.ConstellationGraphAcyclic
open SimpleGraph

variable {M : ℕ}

/-- Decidability of `IsUnit` on the finite ring `ZMod M`: `IsUnit a ↔ ∃ b, a * b = 1`, a decidable
finite existential. -/
instance instDecidableIsUnitZMod [NeZero M] (a : ZMod M) : Decidable (IsUnit a) :=
  decidable_of_iff _ isUnit_iff_exists_inv.symm

/-- Decidability of twin-admissibility on `ZMod M`. -/
instance instDecidableTwinAdm [NeZero M] : DecidablePred (fun a : ZMod M => twinAdm a) :=
  fun a => decidable_of_iff (IsUnit a ∧ IsUnit (a + 2)) Iff.rfl

/-- Decidability of `+3`-adjacency on `ZMod M`. -/
instance instDecidableRelPlusThree [NeZero M] : DecidableRel (plusThreeGraph M).Adj :=
  fun a b => decidable_of_iff ((b - a = 3 ∨ a - b = 3) ∧ a ≠ b) Iff.rfl

/-- **The twin-admissible induced `+3` graph** `G`. Vertices are the twin-admissible residues;
edges are the `±3` steps of the flow restricted to those vertices. -/
def G (M : ℕ) : SimpleGraph {a : ZMod M // twinAdm a} :=
  SimpleGraph.induce {a : ZMod M | twinAdm a} (plusThreeGraph M)

/-- Adjacency in `G` is exactly `+3`-adjacency of the underlying residues. -/
theorem G_adj {v w : {a : ZMod M // twinAdm a}} :
    (G M).Adj v w ↔ (plusThreeGraph M).Adj (v : ZMod M) (w : ZMod M) := by
  unfold G SimpleGraph.induce
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]

/-- Decidability of adjacency in `G` (used for the neighbour-finset / degree). -/
instance instDecidableRelG [NeZero M] : DecidableRel (G M).Adj :=
  fun v w => decidable_of_iff _ G_adj.symm

/-- **Theorem 1 — bounded degree.** Every vertex of the twin-admissible `+3` graph `G` has degree at
most `2`: its neighbours inject into the 2-element set `{↑v+3, ↑v-3}` by `plus_three_neighbourhood`.
-/
theorem induced_degree_le_two [NeZero M] (v : {a : ZMod M // twinAdm a}) :
    (G M).degree v ≤ 2 := by
  have key : ((G M).neighborFinset v).card ≤ 2 := by
    have hsub : ∀ w ∈ (G M).neighborFinset v,
        (Subtype.val w : ZMod M) ∈
          ({(↑v + 3 : ZMod M), (↑v : ZMod M) - 3} : Finset (ZMod M)) := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, G_adj] at hw
      exact plusThreeGraph_neighbour hw
    have hcard : ((G M).neighborFinset v).card ≤
        ({(↑v + 3 : ZMod M), (↑v : ZMod M) - 3} : Finset (ZMod M)).card :=
      Finset.card_le_card_of_injOn Subtype.val hsub Subtype.coe_injective.injOn
    refine hcard.trans ?_
    refine (Finset.card_insert_le _ _).trans ?_
    norm_num [Finset.card_singleton]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact key

/-- **Theorem 2 — forest of paths.** For `Nat.Coprime 3 M` and `1 < M`, the twin-admissible `+3`
graph `G` is acyclic and has maximum degree ≤ 2. A finite acyclic graph with `Δ ≤ 2` is exactly a
disjoint union of paths, so this is the complete structural statement that `G` is a forest of paths.
-/
theorem forest_of_paths [NeZero M] (h3 : Nat.Coprime 3 M) (hM : 1 < M) :
    (G M).IsAcyclic ∧ ∀ v, (G M).degree v ≤ 2 :=
  ⟨twin_admissible_induced_acyclic M h3 hM, fun v => induced_degree_le_two v⟩

/-- **Theorem 3 (chain form) — components have at most 3 vertices.** For `5 ∣ M`, four vertices of
`G` linked in a `+3` progression cannot exist: their underlying residues would be `a, a+3, a+6, a+9`,
all twin-admissible, contradicting `twin_no_four_run`. Since every path component of `G` is a `+3`
run of admissible vertices, this caps each component at ≤ 3 vertices — the `P₁/P₂/P₃` cap. -/
theorem no_four_vertex_plus_three_chain [NeZero M] (h5 : 5 ∣ M)
    (v0 v1 v2 v3 : {a : ZMod M // twinAdm a})
    (h01 : (v1 : ZMod M) - v0 = 3) (h12 : (v2 : ZMod M) - v1 = 3)
    (h23 : (v3 : ZMod M) - v2 = 3) : False := by
  have e1 : (v1 : ZMod M) = (v0 : ZMod M) + 3 := by linear_combination h01
  have e2 : (v2 : ZMod M) = (v0 : ZMod M) + 6 := by linear_combination h12 + h01
  have e3 : (v3 : ZMod M) = (v0 : ZMod M) + 9 := by linear_combination h23 + h12 + h01
  exact twin_no_four_run M h5 (v0 : ZMod M) ⟨v0.2, e1 ▸ v1.2, e2 ▸ v2.2, e3 ▸ v3.2⟩

/-- **Theorem 3 (arithmetic form) — the run cap.** Direct re-statement of `twin_no_four_run`: for
`5 ∣ M`, no residue `a` has all four of `a, a+3, a+6, a+9` twin-admissible. Equivalently, every
twin-admissible `+3`-run — hence every path component of `G` — has length ≤ 3. -/
theorem no_four_admissible_run [NeZero M] (h5 : 5 ∣ M) (a : ZMod M) :
    ¬ (twinAdm a ∧ twinAdm (a + 3) ∧ twinAdm (a + 6) ∧ twinAdm (a + 9)) :=
  twin_no_four_run M h5 a

end Brockian.ConstellationPaths
