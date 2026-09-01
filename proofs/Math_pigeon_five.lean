/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pigeonhole for five two-valued items: among five booleans, some three of them
(at three distinct positions) are equal. -/
theorem pigeon_five (a b c d e : Bool) :
    (a = b ∧ b = c) ∨ (a = b ∧ b = d) ∨ (a = b ∧ b = e) ∨
    (a = c ∧ c = d) ∨ (a = c ∧ c = e) ∨ (a = d ∧ d = e) ∨
    (b = c ∧ c = d) ∨ (b = c ∧ c = e) ∨ (b = d ∧ d = e) ∨
    (c = d ∧ d = e) := by
  decide +revert

/-- The core step of the Ramsey argument: if the three edges from the vertex `0`
to three further distinct vertices `p`, `q`, `r` all have the same colour, then a
monochromatic triangle exists (either using `0`, or the triangle `p q r`). -/
theorem mono_triangle_of_three_same (col : Fin 6 → Fin 6 → Bool) (p q r : Fin 6)
    (h0p : (0 : Fin 6) ≠ p) (h0q : (0 : Fin 6) ≠ q) (h0r : (0 : Fin 6) ≠ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (e1 : col 0 p = col 0 q) (e2 : col 0 q = col 0 r) :
    ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      col x y = col x z ∧ col x y = col y z := by
  by_cases hA : col p q = col 0 p
  · exact ⟨0, p, q, h0p, h0q, hpq, e1, hA.symm⟩
  · by_cases hB : col p r = col 0 p
    · exact ⟨0, p, r, h0p, h0r, hpr, e1.trans e2, hB.symm⟩
    · by_cases hC : col q r = col 0 p
      · exact ⟨0, q, r, h0q, h0r, hqr, e2, by rw [hC, e1]⟩
      · -- all three edges among `p`, `q`, `r` avoid the colour `col 0 p`,
        -- hence they all carry the other colour
        refine ⟨p, q, r, hpq, hpr, hqr, ?_, ?_⟩
        · cases hx : col 0 p <;> rw [hx] at hA hB <;>
            simp only [Bool.not_eq_false, Bool.not_eq_true] at hA hB <;>
            rw [hA, hB]
        · cases hx : col 0 p <;> rw [hx] at hA hC <;>
            simp only [Bool.not_eq_false, Bool.not_eq_true] at hA hC <;>
            rw [hA, hC]

/-- The pentagon (5-cycle) colouring of the edges of `K₅`: the edge `{i, j}` is
coloured `true` exactly when `i` and `j` are consecutive modulo `5`. -/
def pent (i j : Fin 5) : Bool :=
  decide ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)

theorem pent_symm : ∀ i j : Fin 5, pent i j = pent j i := by decide

theorem pent_no_mono_triangle : ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
    ¬ (pent x y = pent x z ∧ pent x y = pent y z) := by decide

/-- **R(3,3) = 6.**

First component: every 2-colouring `col` of the edges of the complete graph `K₆`
(a symmetric `Bool`-valued function on the vertices `Fin 6`) contains a
monochromatic triangle, i.e. three distinct vertices `x`, `y`, `z` whose three
connecting edges all get the same colour.

Second component: there is a 2-colouring of the edges of `K₅` (the pentagon
colouring) with no monochromatic triangle, so 6 is optimal.

(The symmetry hypothesis in the first component reflects that colourings are
colourings of *edges*; the proof given here does not actually need it.) -/
theorem ramsey_3_3 :
    (∀ col : Fin 6 → Fin 6 → Bool, (∀ i j, col i j = col j i) →
      ∃ x y z : Fin 6, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        col x y = col x z ∧ col x y = col y z) ∧
    (∃ col : Fin 5 → Fin 5 → Bool, (∀ i j, col i j = col j i) ∧
      ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
        ¬ (col x y = col x z ∧ col x y = col y z)) := by
  refine ⟨fun col _ => ?_, ⟨pent, pent_symm, pent_no_mono_triangle⟩⟩
  rcases pigeon_five (col 0 1) (col 0 2) (col 0 3) (col 0 4) (col 0 5) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mono_triangle_of_three_same col 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 2 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 2 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 1 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 2 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 2 3 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 2 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2
  · exact mono_triangle_of_three_same col 3 4 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2

end Math

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

