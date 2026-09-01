import Mathlib

/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
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

namespace Math

/-- Boolean core of the pigeonhole/case analysis for `R(3,3) ≤ 6`: for any assignment of two
colours to the fifteen edges of `K₆` (edge `pq` for `p < q` is the variable listed in
lexicographic order), one of the twenty triangles is monochromatic. -/
theorem ramsey_bool_core : ∀ a b c d e f g h i j k l m n o : Bool,
    (((a == b) && (a == f)) || ((a == c) && (a == g)) || ((a == d) && (a == h)) ||
      ((a == e) && (a == i)) ||
    ((b == c) && (b == j)) || ((b == d) && (b == k)) || ((b == e) && (b == l)) ||
    ((c == d) && (c == m)) || ((c == e) && (c == n)) || ((d == e) && (d == o)) ||
    ((f == g) && (f == j)) || ((f == h) && (f == k)) || ((f == i) && (f == l)) ||
    ((g == h) && (g == m)) || ((g == i) && (g == n)) || ((h == i) && (h == o)) ||
    ((j == k) && (j == m)) || ((j == l) && (j == n)) || ((k == l) && (k == o)) ||
    ((m == n) && (m == o))) = true := by decide

/-- The "pentagon" 2-colouring of the edges of `K₅`: an edge is coloured `true` exactly when its
endpoints are consecutive modulo `5`. -/
noncomputable def pentagonColoring : Sym2 (Fin 5) → Bool :=
  Sym2.lift ⟨fun i j => ((i.val + 1) % 5 == j.val) || ((j.val + 1) % 5 == i.val), by decide⟩

/-- **R(3,3) = 6.**  Every 2-colouring of the edges of `K₆` contains a monochromatic triangle,
while there is a 2-colouring of the edges of `K₅` with no monochromatic triangle. -/
theorem ramsey_3_3 :
    (∀ c : Sym2 (Fin 6) → Bool, ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        c s(i, j) = c s(i, k) ∧ c s(i, j) = c s(j, k)) ∧
    (∃ c : Sym2 (Fin 5) → Bool, ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
        ¬(c s(i, j) = c s(i, k) ∧ c s(i, j) = c s(j, k))) := by
  constructor
  · intro c
    have H := ramsey_bool_core (c s(0, 1)) (c s(0, 2)) (c s(0, 3)) (c s(0, 4)) (c s(0, 5))
      (c s(1, 2)) (c s(1, 3)) (c s(1, 4)) (c s(1, 5)) (c s(2, 3)) (c s(2, 4)) (c s(2, 5))
      (c s(3, 4)) (c s(3, 5)) (c s(4, 5))
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at H
    casesm* _ ∨ _
    all_goals exact ⟨_, _, _, by decide, by decide, by decide, H.1, H.2⟩
  · exact ⟨pentagonColoring, by decide⟩

end Math

