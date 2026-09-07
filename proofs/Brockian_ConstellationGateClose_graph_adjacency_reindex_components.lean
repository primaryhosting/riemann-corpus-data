import Mathlib
import Brockian.ConstellationPaths
import Brockian.GraphComponentMatrix

/-
# Constellation sieve: adjacency matrix to connected-component blocks

This module applies the general finite-graph component matrix decomposition to the
twin-admissible `+3` graph. It closes the matrix-infrastructure step: both the adjacency matrix and
the graph Hamiltonian `2 * I - A` reindex to dependent block diagonals, and the Hamiltonian
characteristic polynomial is exactly the product of the characteristic polynomials of its actual
connected-component blocks.

The separate combinatorial task of identifying each component block with `H1`, `H2`, or `H3` and
grouping those factors by the arithmetic multiplicities is not asserted here.
-/

namespace Brockian.ConstellationGateClose

open Matrix
open Brockian.ConstellationGraph
open Brockian.ConstellationPaths
open Brockian.GraphComponentMatrix

noncomputable section

local instance instDecidableEqGraphConnectedComponent (M : Nat) [NeZero M] :
    DecidableEq (G M).ConnectedComponent :=
  Classical.decEq _

/-- The graph Hamiltonian `2 * I - A` of the twin-admissible `+3` graph. -/
def graphHamiltonian (M : Nat) [NeZero M] :
    Matrix {a : ZMod M // twinAdm a} {a : ZMod M // twinAdm a} Real :=
  shiftedAdjacency (G M) (2 : Real)

/-- The twin graph adjacency matrix, reindexed by its connected components, is exactly the
dependent block diagonal of the induced component adjacency matrices. -/
theorem graph_adjacency_reindex_components (M : Nat) [NeZero M] :
    Matrix.reindex (componentEquiv (G M)) (componentEquiv (G M)) ((G M).adjMatrix Real) =
      Matrix.blockDiagonal'
        (fun c : (G M).ConnectedComponent => (componentGraph (G M) c).adjMatrix Real) :=
  adjMatrix_reindex_components (R := Real) (G M)

/-- The twin graph Hamiltonian reindexes to the dependent block diagonal of its component
Hamiltonians. -/
theorem graph_hamiltonian_reindex_components (M : Nat) [NeZero M] :
    Matrix.reindex (componentEquiv (G M)) (componentEquiv (G M)) (graphHamiltonian M) =
      Matrix.blockDiagonal'
        (fun c : (G M).ConnectedComponent =>
          shiftedAdjacency (componentGraph (G M) c) (2 : Real)) := by
  simpa only [graphHamiltonian] using
    shiftedAdjacency_reindex_components (R := Real) (G M) (2 : Real)

/-- The exact connected-component characteristic-polynomial factorization of the twin graph
Hamiltonian. -/
theorem graph_hamiltonian_charpoly_components (M : Nat) [NeZero M] :
    (graphHamiltonian M).charpoly =
      ∏ c : (G M).ConnectedComponent,
        (shiftedAdjacency (componentGraph (G M) c) (2 : Real)).charpoly := by
  simpa only [graphHamiltonian] using
    shiftedAdjacency_charpoly_components (R := Real) (G M) (2 : Real)

end


end Brockian.ConstellationGateClose
