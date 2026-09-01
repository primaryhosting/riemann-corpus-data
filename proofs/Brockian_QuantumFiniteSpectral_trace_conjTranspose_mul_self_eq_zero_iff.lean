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

/-
# Finite-dimensional spectral bridges for quantum mechanics

Composite bridge lemmas over `Matrix`/`EuclideanSpace` that downstream Brockian
results (spectral scaffolds, Hilbert-Polya style operator arguments) can consume.
Everything here is finite and algebraic: no asymptotics, no O-notation.
-/
import Mathlib

namespace Brockian.QuantumFiniteSpectral

open Matrix

theorem trace_conjTranspose_mul_self_eq_zero_iff {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (Aᴴ * A).trace = 0 ↔ A = 0 := by
  open ComplexOrder in
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff

end Brockian.QuantumFiniteSpectral

