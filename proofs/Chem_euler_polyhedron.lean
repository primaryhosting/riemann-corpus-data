/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/--
Combinatorial model of the plane graph obtained from a convex polyhedron
(for instance a fullerene cage) by a Schlegel projection: the vertices and edges of the
polyhedron are drawn in the plane, one distinguished face becoming the unbounded region,
so that the number of regions of the drawing equals the number of faces of the polyhedron.

`PlaneGraph V E F` says that a connected plane graph with `V` vertices, `E` edges and
`F` faces (regions, the unbounded one included) can be built up from a single point by
the two standard plane operations:

* attaching a new vertex along a new edge (this does not change the number of regions);
* drawing a new edge between two existing vertices (this splits one region into two).

Every connected plane graph arises in this way: build a spanning tree first, then draw
the remaining edges one by one.
-/
inductive PlaneGraph : Nat → Nat → Nat → Prop where
  /-- A single vertex, no edges, one (unbounded) region. -/
  | point : PlaneGraph 1 0 1
  /-- Attach a pendant vertex along a new edge: the number of regions is unchanged. -/
  | addVertex {V E F : Nat} : PlaneGraph V E F → PlaneGraph (V + 1) (E + 1) F
  /-- Draw a new edge between two existing vertices: one region is split in two. -/
  | addEdge {V E F : Nat} : PlaneGraph V E F → PlaneGraph V (E + 1) (F + 1)

/-- Euler's formula in the natural numbers: `V + F = E + 2`. -/
theorem euler_polyhedron_nat {V E F : Nat} (h : PlaneGraph V E F) : V + F = E + 2 := by
  induction h with
  | point => rfl
  | addVertex _ ih => omega
  | addEdge _ ih => omega

/--
**Euler's polyhedron formula.** For a convex polyhedron (e.g. a fullerene cage) with
`V` vertices, `E` edges and `F` faces, one has `V - E + F = 2`.
-/
theorem euler_polyhedron {V E F : Nat} (h : PlaneGraph V E F) :
    (V : Int) - (E : Int) + (F : Int) = 2 := by
  have := euler_polyhedron_nat h
  omega

/-- A tree with `n + 1` vertices: it has `n` edges and a single region. -/
theorem planeGraph_tree (n : Nat) : PlaneGraph (n + 1) n 1 := by
  induction n with
  | zero => exact PlaneGraph.point
  | succ n ih => exact ih.addVertex

/-- Drawing `k` further edges creates `k` further regions. -/
theorem planeGraph_addEdges {V E F : Nat} (h : PlaneGraph V E F) (k : Nat) :
    PlaneGraph V (E + k) (F + k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.addEdge

/-- Realizability: for every number of vertices `n + 1` and every number of edges
`n + k` at least `n`, there is a connected plane graph with those counts; its number
of faces is then forced to be `1 + k = (n + k) - (n + 1) + 2`. -/
theorem planeGraph_exists (n k : Nat) : PlaneGraph (n + 1) (n + k) (1 + k) :=
  planeGraph_addEdges (planeGraph_tree n) k

/-- The tetrahedron: `4 - 6 + 4 = 2`. -/
example : PlaneGraph 4 6 4 := planeGraph_exists 3 3

/-- The cube: `8 - 12 + 6 = 2`. -/
example : PlaneGraph 8 12 6 := planeGraph_exists 7 5

/-- The dodecahedron: `20 - 30 + 12 = 2`. -/
example : PlaneGraph 20 30 12 := planeGraph_exists 19 11

/-- The buckminsterfullerene cage C₆₀: `60 - 90 + 32 = 2`. -/
theorem planeGraph_C60 : PlaneGraph 60 90 32 := planeGraph_exists 59 31

/--
**Fullerenes have exactly twelve pentagons.**

If a polyhedral cage is trivalent (every vertex lies on exactly three edges, so
`2 * E = 3 * V`) and each of its `F = p + h` faces is a pentagon or a hexagon (so
`2 * E = 5 * p + 6 * h`), then the number `p` of pentagonal faces equals `12`,
whatever the number `h` of hexagons. This is a direct consequence of Euler's formula.
-/
theorem fullerene_twelve_pentagons {V E F p h : Nat} (hg : PlaneGraph V E F)
    (hdeg : 2 * E = 3 * V) (hF : F = p + h) (hsize : 2 * E = 5 * p + 6 * h) :
    p = 12 := by
  have he := euler_polyhedron_nat hg
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

