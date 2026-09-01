import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Polynomial

namespace Chem

#check (SimpleGraph.cycleGraph 10).adjMatrix ℂ
#check @Matrix.charpoly_diagonal
#check @Matrix.charpoly_units_conj
#check @Matrix.det_vandermonde_ne_zero_iff
#check @Complex.isPrimitiveRoot_exp
#check @Matrix.mem_spectrum_iff_isRoot_charpoly

example (i j : Fin 10) : (SimpleGraph.cycleGraph 10).Adj i j ↔ (i - j = 1 ∨ j - i = 1) := by
  simp [SimpleGraph.cycleGraph]

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

