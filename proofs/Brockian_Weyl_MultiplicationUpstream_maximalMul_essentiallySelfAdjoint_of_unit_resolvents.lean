/-
  General essential-self-adjointness criterion for maximal multiplication
  operators.  This module deliberately contains no Brockian potential or
  number-theoretic definitions; it is an extraction candidate for Mathlib.
-/
import Brockian.WeylMaximalMultiplication

open MeasureTheory

namespace Brockian.Weyl.MultiplicationUpstream

open Brockian.Weyl.Cayley
open Brockian.Weyl.MaximalMultiplication

variable {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}

/-- A densely defined maximal multiplication operator is essentially
self-adjoint once multiplication by the inverses of its two unit shifts is
bounded on `L2`.  The inverse identities give surjectivity of both shifted
ranges, while density of the multiplication domain supplies the hypothesis
of the von Neumann range criterion. -/
theorem maximalMul_essentiallySelfAdjoint_of_unit_resolvents
    (g rAdd rSub : alpha -> Complex)
    (hd : Dense ((maximalMul (μ := mu) g).domain : Set (Lp Complex 2 mu)))
    (hrAdd : MemLp rAdd ∞ mu)
    (hrSub : MemLp rSub ∞ mu)
    (hAdd : forall x, (g x - (-Complex.I)) * rAdd x = 1)
    (hSub : forall x, (g x - Complex.I) * rSub x = 1) :
    Brockian.Weyl.Operator.EssentiallySelfAdjoint (maximalMul (μ := mu) g) := by
  rw [essentiallySelfAdjoint_iff hd]
  constructor
  · rw [rangeAddI,
      rangeSMulSub_maximalMul_eq_top g rAdd (-Complex.I) hrAdd hAdd]
    exact dense_univ
  · rw [rangeSubI,
      rangeSMulSub_maximalMul_eq_top g rSub Complex.I hrSub hSub]
    exact dense_univ

end Brockian.Weyl.MultiplicationUpstream
