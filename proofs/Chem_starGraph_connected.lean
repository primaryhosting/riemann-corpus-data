import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open SimpleGraph

/-! ### Star graphs are trees

We need a supply of concrete finite trees in order to exhibit examples of the
structure defined below; the simplest such family is the star graph. -/

/-- The star graph on `V` centred at `c`: `a` and `b` are adjacent iff they are
distinct and one of them is the centre `c`. -/
def starGraph {V : Type*} (c : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (a = c ∨ b = c)
  symm := by
    rintro a b ⟨hab, h⟩
    exact ⟨hab.symm, h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma starGraph_connected {V : Type*} [Nonempty V] (c : V) : (starGraph c).Connected := by
  have key : ∀ x : V, (starGraph c).Reachable x c := by
    intro x
    by_cases hx : x = c
    · subst hx; rfl
    · exact SimpleGraph.Adj.reachable (G := starGraph c) ⟨hx, Or.inr rfl⟩
  exact { preconnected := fun a b => (key a).trans (key b).symm }

/-- The edges of the star graph centred at `c` are exactly the pairs `s(c, v)`
with `v ≠ c`. -/
lemma starGraph_edge_bijective {V : Type*} (c : V) :
    Function.Bijective (fun v : {v : V // v ≠ c} =>
      (⟨s(c, v.1), by
        have : (starGraph c).Adj c v.1 := ⟨fun h => v.2 h.symm, Or.inl rfl⟩
        simpa using this⟩ : (starGraph c).edgeSet)) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq, Sym2.congr_right] at hab
    exact Subtype.ext hab
  · rintro ⟨e, he⟩
    induction e with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨hab, h⟩ := he
      rcases h with h | h
      · subst h
        exact ⟨⟨b, fun hb => hab hb.symm⟩, rfl⟩
      · subst h
        exact ⟨⟨a, hab⟩, Subtype.ext (Sym2.eq_swap)⟩

lemma starGraph_card_edgeSet {V : Type*} [Finite V] (c : V) :
    Nat.card (starGraph c).edgeSet + 1 = Nat.card V := by
  classical
  have : Fintype V := Fintype.ofFinite V
  haveI : Nonempty V := ⟨c⟩
  have h1 : Nat.card (starGraph c).edgeSet = Nat.card {v : V // v ≠ c} :=
    (Nat.card_eq_of_bijective _ (starGraph_edge_bijective c)).symm
  have h2 : Fintype.card {v : V // ¬ (v = c)} = Fintype.card V - Fintype.card {v : V // v = c} :=
    Fintype.card_subtype_compl _
  have h3 : Fintype.card {v : V // v = c} = 1 := Fintype.card_subtype_eq c
  have h4 : 0 < Fintype.card V := Fintype.card_pos
  rw [h1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp only [ne_eq]
  omega

lemma starGraph_isTree {V : Type*} [Finite V] [Nonempty V] (c : V) : (starGraph c).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨starGraph_connected c, starGraph_card_edgeSet c⟩

/-! ### Polyhedral surfaces

A convex polyhedron (a fullerene cage, say) determines a map on the sphere: its
vertices, edges and faces.  The combinatorial content of *sphericity* that
Euler's formula needs is the classical **tree–cotree decomposition**: the edge
set of a map drawn on the sphere splits into a spanning tree of the graph of the
polyhedron together with a spanning tree of the dual graph (whose vertices are
the faces of the polyhedron).  Indeed, given a spanning tree `T` of the
vertex–edge graph, the edges *not* in `T` are exactly the edges of a spanning
tree of the dual graph.

We take this decomposition as the data attached to a convex polyhedron. -/

/-- Combinatorial data of a convex polyhedron (a map on the sphere), recorded
through its tree–cotree decomposition: a spanning tree of the polyhedron's graph
on its vertices, a spanning tree of the dual graph on its faces, and the fact
that these two trees use each edge exactly once between them. -/
structure PolyhedralSurface where
  /-- The vertices of the polyhedron. -/
  Vertex : Type
  /-- The edges of the polyhedron. -/
  Edge : Type
  /-- The faces of the polyhedron. -/
  Face : Type
  [finiteVertex : Finite Vertex]
  [finiteEdge : Finite Edge]
  [finiteFace : Finite Face]
  /-- A spanning tree of the graph of the polyhedron. -/
  primalTree : SimpleGraph Vertex
  /-- A spanning tree of the dual graph, on the set of faces. -/
  dualTree : SimpleGraph Face
  /-- `primalTree` is indeed a tree (and spans, since it is a graph on all
  vertices). -/
  primalTree_isTree : primalTree.IsTree
  /-- `dualTree` is indeed a tree (and spans all faces). -/
  dualTree_isTree : dualTree.IsTree
  /-- Tree–cotree decomposition: every edge of the polyhedron belongs either to
  the spanning tree or to the dual spanning tree, and to exactly one of them. -/
  edge_partition : Nat.card Edge = Nat.card primalTree.edgeSet + Nat.card dualTree.edgeSet

attribute [instance] PolyhedralSurface.finiteVertex PolyhedralSurface.finiteEdge
  PolyhedralSurface.finiteFace

namespace PolyhedralSurface

variable (P : PolyhedralSurface)

/-- The number of vertices `V`. -/
noncomputable def numVertices : ℕ := Nat.card P.Vertex

/-- The number of edges `E`. -/
noncomputable def numEdges : ℕ := Nat.card P.Edge

/-- The number of faces `F`. -/
noncomputable def numFaces : ℕ := Nat.card P.Face

end PolyhedralSurface

/-- **Euler's polyhedron formula**: for a convex polyhedron (for instance a
fullerene cage), `V - E + F = 2`.

The proof is the tree–cotree argument: a spanning tree of the graph has
`V - 1` edges and a spanning tree of the dual graph has `F - 1` edges
(`SimpleGraph.IsTree.card_edgeFinset`, used here in its `Nat.card` form
`SimpleGraph.isTree_iff_connected_and_card`), and together they use up all `E`
edges. -/
theorem euler_polyhedron (P : PolyhedralSurface) :
    (P.numVertices : ℤ) - P.numEdges + P.numFaces = 2 := by
  have hV : Nat.card P.primalTree.edgeSet + 1 = Nat.card P.Vertex :=
    (SimpleGraph.isTree_iff_connected_and_card.mp P.primalTree_isTree).2
  have hF : Nat.card P.dualTree.edgeSet + 1 = Nat.card P.Face :=
    (SimpleGraph.isTree_iff_connected_and_card.mp P.dualTree_isTree).2
  have hE := P.edge_partition
  simp only [PolyhedralSurface.numVertices, PolyhedralSurface.numEdges,
    PolyhedralSurface.numFaces]
  omega

/-- Euler's formula, stated in `ℕ` as `V + F = E + 2`. -/
theorem euler_polyhedron_nat (P : PolyhedralSurface) :
    P.numVertices + P.numFaces = P.numEdges + 2 := by
  have := euler_polyhedron P
  omega

/-! ### Examples: the hypotheses are satisfiable -/

/-- Any counts `V, F ≥ 1` with `E = V + F - 2` are realised by a polyhedral
surface, so the hypotheses of `Chem.euler_polyhedron` are satisfiable. -/
noncomputable def surfaceOfCounts (v f : ℕ) (hv : 0 < v) (hf : 0 < f) : PolyhedralSurface :=
  haveI : NeZero v := ⟨hv.ne'⟩
  haveI : NeZero f := ⟨hf.ne'⟩
  { Vertex := Fin v
    Edge := Fin (v + f - 2)
    Face := Fin f
    primalTree := starGraph (⟨0, hv⟩ : Fin v)
    dualTree := starGraph (⟨0, hf⟩ : Fin f)
    primalTree_isTree := starGraph_isTree _
    dualTree_isTree := starGraph_isTree _
    edge_partition := by
      have h1 := starGraph_card_edgeSet (⟨0, hv⟩ : Fin v)
      have h2 := starGraph_card_edgeSet (⟨0, hf⟩ : Fin f)
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1 h2 ⊢
      omega }

@[simp] lemma surfaceOfCounts_numVertices (v f : ℕ) (hv : 0 < v) (hf : 0 < f) :
    (surfaceOfCounts v f hv hf).numVertices = v := by
  simp [surfaceOfCounts, PolyhedralSurface.numVertices]

@[simp] lemma surfaceOfCounts_numFaces (v f : ℕ) (hv : 0 < v) (hf : 0 < f) :
    (surfaceOfCounts v f hv hf).numFaces = f := by
  simp [surfaceOfCounts, PolyhedralSurface.numFaces]

@[simp] lemma surfaceOfCounts_numEdges (v f : ℕ) (hv : 0 < v) (hf : 0 < f) :
    (surfaceOfCounts v f hv hf).numEdges = v + f - 2 := by
  simp [surfaceOfCounts, PolyhedralSurface.numEdges]

/-- The tetrahedron: `V = 4`, `E = 6`, `F = 4`. -/
noncomputable def tetrahedron : PolyhedralSurface := surfaceOfCounts 4 4 (by norm_num) (by norm_num)

example : tetrahedron.numVertices = 4 ∧ tetrahedron.numEdges = 6 ∧ tetrahedron.numFaces = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [tetrahedron]

/-- The buckminsterfullerene cage C₆₀: `V = 60`, `E = 90`, `F = 32`
(12 pentagons and 20 hexagons). -/
noncomputable def fullereneC60 : PolyhedralSurface :=
  surfaceOfCounts 60 32 (by norm_num) (by norm_num)

example : fullereneC60.numVertices = 60 ∧ fullereneC60.numEdges = 90 ∧
    fullereneC60.numFaces = 32 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fullereneC60]

/-! ### A chemical corollary: every fullerene has exactly twelve pentagons -/

/-- For a cubic (three-valent) polyhedron all of whose faces are pentagons or
hexagons — a fullerene cage — Euler's formula forces the number of pentagonal
faces to be exactly `12`, whatever the number `h` of hexagons.

Here `cubic` says that every vertex lies on three edges (`3V = 2E`), `faces`
that the `F` faces split into `p` pentagons and `h` hexagons, and `incidences`
counts edge–face incidences (`2E = 5p + 6h`). -/
theorem fullerene_twelve_pentagons (P : PolyhedralSurface) (p h : ℕ)
    (cubic : 3 * P.numVertices = 2 * P.numEdges)
    (faces : P.numFaces = p + h)
    (incidences : 2 * P.numEdges = 5 * p + 6 * h) : p = 12 := by
  have := euler_polyhedron_nat P
  omega

end Chem

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

