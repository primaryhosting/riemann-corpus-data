/-!
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- The constant ray-step law: each successive multiple of `s` advances the ray index
by `s % 5`. -/
theorem ray_step (s k : Nat) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  induction k with
  | zero => simp
  | succ n _ => rw [Nat.add_mul, Nat.one_mul, Nat.add_mod]

/-- The multiples of a stride `s` walk the five rays in a fixed cyclic order determined
by `s % 5`: strides `≡ 2 (mod 5)` trace the pentagram order `(2,4,1,3,0)`, strides
`≡ 3` its mirror `(3,1,4,2,0)`, strides `≡ 1` the pentagon `(1,2,3,4,0)`, strides `≡ 4`
its mirror `(4,3,2,1,0)`, and strides `≡ 0` never leave ray `0`. -/
theorem stride_ray_walk_classification :
    (∀ s k : Nat, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : Nat, s % 5 = 2 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [2, 4, 1, 3, 0]) ∧
    (∀ s : Nat, s % 5 = 3 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [3, 1, 4, 2, 0]) ∧
    (∀ s : Nat, s % 5 = 1 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0]) ∧
    (∀ s : Nat, s % 5 = 4 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0]) ∧
    (∀ s : Nat, s % 5 = 0 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0]) := by
  refine ⟨ray_step, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro s hs
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.cons.injEq, and_true]
    omega

end Brockian.ConeLine

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

