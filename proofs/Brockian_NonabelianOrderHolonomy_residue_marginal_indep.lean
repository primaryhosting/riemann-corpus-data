import Mathlib

/-! # Order-dependent depth-holonomy over a NONABELIAN fiber.

Every depth-holonomy separation proved so far (over `ZMod n` fibers, and even the single-seam
`DihedralGroup 3` fiber) is *order-independent*: winding the loop once left-multiplies the fiber
by a single fixed group element, and the abelian structure means the seams commute.

Here we place TWO seams on the residue cycle `ZMod 3`, contributing group elements `a` (at
residue 1) and `b` (at residue 2) of the nonabelian symmetric group `S₃ = Equiv.Perm (Fin 3)`,
acting by LEFT-multiplication. Winding the loop once from the basepoint therefore composes the
two seam elements into the *word* `b * a`. Because `S₃` is nonabelian, swapping which seam gets
`a` and which gets `b` — i.e. reversing the traversal order of the two seams — changes the
holonomy: `b * a ≠ a * b`. This order-dependence is a genuinely new structural fact, invisible
to every abelian ZMod-fiber result. -/

namespace Brockian.NonabelianOrderHolonomy

/-- Transfer operator over `ZMod 3 × S₃`. Advance the residue by one, and at each seam
    left-multiply the fiber: seam at residue 1 contributes `a`, seam at residue 2 contributes
    `b`. Only one guard is ever active per step, so this picks exactly the seam element for the
    current residue (identity `1` off the seams). -/
def K (a b : Equiv.Perm (Fin 3)) (x : ZMod 3 × Equiv.Perm (Fin 3)) :
    ZMod 3 × Equiv.Perm (Fin 3) :=
  (x.1 + 1, (if x.1 = 1 then a else 1) * (if x.1 = 2 then b else 1) * x.2)

/-- **Residue marginal is holonomy-blind.** The one-step residue transition is `j ↦ j + 1` for
    every choice of seam elements `a, b`: residue-class (mod-3) Fourier analysis cannot see the
    depth holonomy. -/
theorem residue_marginal_indep (a b : Equiv.Perm (Fin 3)) (x : ZMod 3 × Equiv.Perm (Fin 3)) :
    (K a b x).1 = x.1 + 1 := rfl

/-- **Loop holonomy is the word `b * a`.** Winding the residue cycle once from any basepoint on
    residue `0` left-multiplies the fiber by the ordered word `b * a`: the loop passes the
    `a`-seam (residue 1) first, then the `b`-seam (residue 2), and left-multiplication stacks the
    later seam on the outside. -/
theorem loop_holonomy (a b g : Equiv.Perm (Fin 3)) :
    (K a b)^[3] (0, g) = (0, b * a * g) := by revert a b g; decide

/-- **Order dependence — the CRUX.** There exist seam elements `a, b` for which reversing the
    two seams changes the holonomy word: `b * a ≠ a * b`. This is impossible over any abelian
    fiber; it is the new structural content of the nonabelian seam. -/
theorem order_dependent :
    ∃ a b : Equiv.Perm (Fin 3), b * a ≠ a * b := by decide

/-- **Holonomy is noncommutative at the basepoint.** Concretely, there are seam elements `a, b`
    such that traversing the loop with the seams in one order lands on a different fiber value
    than traversing with the seams swapped: `(K a b)^[3] (0,1) ≠ (K b a)^[3] (0,1)`. -/
theorem holonomy_noncommutative :
    ∃ a b : Equiv.Perm (Fin 3), (K a b)^[3] (0, 1) ≠ (K b a)^[3] (0, 1) := by decide

/-- **Summary separation.** Every seam pair yields the identical one-step residue transition,
    yet the loop recovers the ordered nonabelian word `b * a`, and that word is order-dependent —
    the holonomy genuinely depends on seam order, unlike every abelian ZMod-fiber case. -/
theorem nonabelian_order_separation :
    (∀ (a b : Equiv.Perm (Fin 3)) x, (K a b x).1 = x.1 + 1) ∧
    (∀ (a b g : Equiv.Perm (Fin 3)), (K a b)^[3] (0, g) = (0, b * a * g)) ∧
    (∃ a b : Equiv.Perm (Fin 3), b * a ≠ a * b) :=
  ⟨residue_marginal_indep, loop_holonomy, order_dependent⟩

end Brockian.NonabelianOrderHolonomy
