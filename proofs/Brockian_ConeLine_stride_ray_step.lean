import Mathlib

/-!
# Stride Ray Walk Classification
Category: Cone Line
Target: Brockian.ConeLine.stride_ray_walk_classification
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- Each successive multiple of the stride `s` advances the ray index by the
constant step `s % 5`. -/
theorem stride_ray_step (s k : ℕ) : ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5 := by
  rw [Nat.add_mul, one_mul, Nat.add_mod]

/-- Stride ≡ 2 (mod 5): the walk traces the pentagram order. -/
theorem stride_walk_two (s : ℕ) (h : s % 5 = 2) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [2, 4, 1, 3, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- Stride ≡ 3 (mod 5): the mirrored pentagram order. -/
theorem stride_walk_three (s : ℕ) (h : s % 5 = 3) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [3, 1, 4, 2, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- Stride ≡ 1 (mod 5): the pentagon order. -/
theorem stride_walk_one (s : ℕ) (h : s % 5 = 1) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- Stride ≡ 4 (mod 5): the mirrored pentagon order. -/
theorem stride_walk_four (s : ℕ) (h : s % 5 = 4) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- Stride ≡ 0 (mod 5): the walk never leaves ray 0. -/
theorem stride_walk_zero (s : ℕ) (h : s % 5 = 0) :
    (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0] := by
  simp [List.range_succ, Nat.mul_mod, h]

/-- **Stride ray walk classification.** The multiples of a stride `s` walk the five rays
with the constant step `s % 5`, and the resulting cyclic order is determined entirely by
the residue `s % 5`: `2` gives the pentagram `(2,4,1,3,0)`, `3` its mirror `(3,1,4,2,0)`,
`1` the pentagon `(1,2,3,4,0)`, `4` its mirror `(4,3,2,1,0)`, and `0` stays on ray `0`. -/
theorem stride_ray_walk_classification :
    (∀ s k : ℕ, ((k + 1) * s) % 5 = (k * s % 5 + s % 5) % 5) ∧
    (∀ s : ℕ, s % 5 = 2 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [2, 4, 1, 3, 0]) ∧
    (∀ s : ℕ, s % 5 = 3 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [3, 1, 4, 2, 0]) ∧
    (∀ s : ℕ, s % 5 = 1 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [1, 2, 3, 4, 0]) ∧
    (∀ s : ℕ, s % 5 = 4 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [4, 3, 2, 1, 0]) ∧
    (∀ s : ℕ, s % 5 = 0 →
      (List.range 5).map (fun k => ((k + 1) * s) % 5) = [0, 0, 0, 0, 0]) :=
  ⟨stride_ray_step, stride_walk_two, stride_walk_three, stride_walk_one,
    stride_walk_four, stride_walk_zero⟩

end Brockian.ConeLine

