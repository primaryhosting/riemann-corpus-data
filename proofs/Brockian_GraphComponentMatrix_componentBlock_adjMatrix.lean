import Mathlib

/-
# Matrices decomposed by graph connected components

For a finite simple graph, the vertex type is canonically equivalent to the dependent sum of the
supports of its connected components. Any matrix whose cross-component entries vanish therefore
reindexes to a dependent block-diagonal matrix. Its characteristic polynomial factors as the
product of the characteristic polynomials of the component blocks.

The final theorems specialize this general result to a graph adjacency matrix and to the shifted
adjacency operator `r * I - A`. They supply the matrix bridge needed by the constellation-sieve
program without assuming anything specific about that graph.
-/

namespace Brockian.GraphComponentMatrix

open Matrix SimpleGraph

noncomputable section

universe u v

variable {V : Type u} {R : Type v} [Fintype V] [DecidableEq V]

local instance instDecidableEqConnectedComponent (G : SimpleGraph V) :
    DecidableEq G.ConnectedComponent :=
  Classical.decEq _

abbrev ComponentFiber (G : SimpleGraph V) (c : G.ConnectedComponent) :=
  {v : V // G.connectedComponentMk v = c}

/-- The graph induced by `G` on the explicit fiber of one connected component. -/
abbrev componentGraph (G : SimpleGraph V) (c : G.ConnectedComponent) :
    SimpleGraph (ComponentFiber G c) :=
  G.induce {v | G.connectedComponentMk v = c}

/-- The canonical equivalence from vertices to the dependent sum of their connected-component
supports. -/
noncomputable def componentEquiv (G : SimpleGraph V) :
    V ≃ Σ c : G.ConnectedComponent, ComponentFiber G c :=
  (Equiv.sigmaFiberEquiv G.connectedComponentMk).symm

@[simp]
theorem componentEquiv_apply (G : SimpleGraph V) (v : V) :
    componentEquiv G v = ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩ :=
  rfl

/-- The principal block of a matrix on one connected component. -/
def componentBlock (G : SimpleGraph V) (A : Matrix V V R) (c : G.ConnectedComponent) :
    Matrix (ComponentFiber G c) (ComponentFiber G c) R :=
  A.submatrix Subtype.val Subtype.val

/-- A matrix with zero entries between distinct connected components becomes a dependent
block-diagonal matrix under the canonical component reindexing. -/
theorem reindex_componentEquiv_eq_blockDiagonal' [Zero R] (G : SimpleGraph V) (A : Matrix V V R)
    (hzero : ∀ i j, G.connectedComponentMk i ≠ G.connectedComponentMk j → A i j = 0) :
    Matrix.reindex (componentEquiv G) (componentEquiv G) A =
      Matrix.blockDiagonal' (fun c => componentBlock G A c) := by
  classical
  ext ⟨c, i⟩ ⟨d, j⟩
  by_cases hcd : c = d
  · subst d
    rw [Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq]
    change A (i : V) (j : V) = A (i : V) (j : V)
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne
      (fun c : G.ConnectedComponent => componentBlock G A c) (k := c) (k' := d) i j hcd,
      Matrix.reindex_apply]
    apply hzero
    intro heq
    apply hcd
    exact i.property.symm.trans (heq.trans j.property)

/-- Characteristic-polynomial factorization for any matrix whose cross-component entries vanish. -/
theorem charpoly_eq_prod_componentBlocks [CommRing R] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Matrix V V R)
    (hzero : ∀ i j, G.connectedComponentMk i ≠ G.connectedComponentMk j → A i j = 0) :
    A.charpoly = ∏ c : G.ConnectedComponent, (componentBlock G A c).charpoly := by
  classical
  letI : LinearOrder G.ConnectedComponent :=
    (Fintype.equivFin G.ConnectedComponent).linearOrder
  have htri : A.BlockTriangular G.connectedComponentMk := by
    intro i j hlt
    exact hzero i j (ne_of_gt hlt)
  rw [htri.charpoly]
  have himage : Finset.image G.connectedComponentMk Finset.univ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    obtain ⟨v, rfl⟩ := Quot.exists_rep c
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  rw [himage]
  apply Finset.prod_congr rfl
  intro c _
  rfl

/-- The adjacency matrix restricted to a component fiber is the adjacency matrix of the induced
component graph. -/
theorem componentBlock_adjMatrix [Zero R] [One R] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) :
    componentBlock G (G.adjMatrix R) c = (componentGraph G c).adjMatrix R := by
  ext i j
  rfl

/-- Adjacency entries vanish between distinct connected components. -/
theorem adjMatrix_eq_zero_of_components_ne [Zero R] [One R] (G : SimpleGraph V)
    [DecidableRel G.Adj] (i j : V)
    (hij : G.connectedComponentMk i ≠ G.connectedComponentMk j) :
    G.adjMatrix R i j = 0 := by
  rw [SimpleGraph.adjMatrix_apply]
  split_ifs with h
  · exact (hij (ConnectedComponent.connectedComponentMk_eq_of_adj h)).elim
  · rfl

/-- Reindexing a graph adjacency matrix by connected component gives the dependent block diagonal
of the component adjacency matrices. -/
theorem adjMatrix_reindex_components [Zero R] [One R] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.reindex (componentEquiv G) (componentEquiv G) (G.adjMatrix R) =
      Matrix.blockDiagonal'
        (fun c : G.ConnectedComponent => (componentGraph G c).adjMatrix R) := by
  calc
    Matrix.reindex (componentEquiv G) (componentEquiv G) (G.adjMatrix R) =
        Matrix.blockDiagonal' (fun c => componentBlock G (G.adjMatrix R) c) :=
      reindex_componentEquiv_eq_blockDiagonal' G (G.adjMatrix R)
        (adjMatrix_eq_zero_of_components_ne G)
    _ = Matrix.blockDiagonal'
        (fun c : G.ConnectedComponent => (componentGraph G c).adjMatrix R) := by
      apply congrArg Matrix.blockDiagonal'
      funext c
      exact componentBlock_adjMatrix G c

/-- The shifted adjacency matrix `r * I - A`. For `r = 2`, this is the graph Hamiltonian used by
the constellation-sieve program. -/
def shiftedAdjacency [Ring R] (G : SimpleGraph V) [DecidableRel G.Adj] (r : R) : Matrix V V R :=
  r • (1 : Matrix V V R) - G.adjMatrix R

/-- Restricting a shifted adjacency matrix to a component commutes with forming the shift. -/
theorem componentBlock_shiftedAdjacency [CommRing R] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : R) (c : G.ConnectedComponent) :
    componentBlock G (shiftedAdjacency G r) c = shiftedAdjacency (componentGraph G c) r := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [componentBlock, shiftedAdjacency, componentGraph]
  · have hval : (i : V) ≠ (j : V) := fun h => hij (Subtype.ext h)
    simp [componentBlock, shiftedAdjacency, componentGraph, hij, hval]
    rfl

/-- Shifted-adjacency entries vanish between distinct connected components. -/
theorem shiftedAdjacency_eq_zero_of_components_ne [CommRing R] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : R) (i j : V)
    (hij : G.connectedComponentMk i ≠ G.connectedComponentMk j) :
    shiftedAdjacency G r i j = 0 := by
  have hne : i ≠ j := fun h => hij (congrArg G.connectedComponentMk h)
  rw [shiftedAdjacency, Matrix.sub_apply, Matrix.smul_apply,
    adjMatrix_eq_zero_of_components_ne G i j hij]
  simp [hne]

/-- The shifted adjacency matrix reindexes to the dependent block diagonal of the shifted
component adjacency matrices. -/
theorem shiftedAdjacency_reindex_components [CommRing R] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : R) :
    Matrix.reindex (componentEquiv G) (componentEquiv G) (shiftedAdjacency G r) =
      Matrix.blockDiagonal'
        (fun c : G.ConnectedComponent => shiftedAdjacency (componentGraph G c) r) := by
  calc
    Matrix.reindex (componentEquiv G) (componentEquiv G) (shiftedAdjacency G r) =
        Matrix.blockDiagonal' (fun c => componentBlock G (shiftedAdjacency G r) c) :=
      reindex_componentEquiv_eq_blockDiagonal' G (shiftedAdjacency G r)
        (shiftedAdjacency_eq_zero_of_components_ne G r)
    _ = Matrix.blockDiagonal'
        (fun c : G.ConnectedComponent => shiftedAdjacency (componentGraph G c) r) := by
      apply congrArg Matrix.blockDiagonal'
      funext c
      exact componentBlock_shiftedAdjacency G r c

/-- The adjacency characteristic polynomial is the product of the characteristic polynomials of
the connected-component adjacency matrices. -/
theorem adjMatrix_charpoly_components [CommRing R] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix R).charpoly =
      ∏ c : G.ConnectedComponent, ((componentGraph G c).adjMatrix R).charpoly := by
  rw [charpoly_eq_prod_componentBlocks G (G.adjMatrix R)
    (adjMatrix_eq_zero_of_components_ne G)]
  apply Finset.prod_congr rfl
  intro c _
  rw [componentBlock_adjMatrix]

/-- The characteristic polynomial of `r * I - A` is the product of the shifted-adjacency
characteristic polynomials of the connected components. -/
theorem shiftedAdjacency_charpoly_components [CommRing R] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : R) :
    (shiftedAdjacency G r).charpoly =
      ∏ c : G.ConnectedComponent, (shiftedAdjacency (componentGraph G c) r).charpoly := by
  rw [charpoly_eq_prod_componentBlocks G (shiftedAdjacency G r)
    (shiftedAdjacency_eq_zero_of_components_ne G r)]
  apply Finset.prod_congr rfl
  intro c _
  rw [componentBlock_shiftedAdjacency]

end

end Brockian.GraphComponentMatrix
