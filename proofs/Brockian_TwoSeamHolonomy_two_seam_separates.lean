import Mathlib

/-! # Two-seam depth-holonomy: holonomy composes ADDITIVELY over multiple seams.

Depth lives in `ZMod 6` over the residue cycle `ZMod 5`. There are TWO seams: at `j = 2`
the depth is incremented by `g`, and at `j = 4` by `h`. One full loop of the residue cycle
crosses each seam exactly once, so the total depth-holonomy is `g + h` — additive over seams. -/

namespace Brockian.TwoSeamHolonomy

/-- `K g h` advances the residue and increments the depth by `g` at seam `j = 2` and by `h`
    at seam `j = 4`. -/
def K (g h : ZMod 6) (x : ZMod 5 × ZMod 6) : ZMod 5 × ZMod 6 :=
  (x.1 + 1, x.2 + (if x.1 = 2 then g else 0) + (if x.1 = 4 then h else 0))

/-- The one-step residue transition is `j ↦ j + 1` for EVERY pair of holonomies `(g, h)`:
    residue-class (mod-5) Fourier analysis is blind to both seam holonomies. -/
theorem residue_marginal_indep (g h : ZMod 6) (x : ZMod 5 × ZMod 6) :
    (K g h x).1 = x.1 + 1 :=
  rfl

/-- **Holonomy composes additively.** One loop of the residue cycle crosses both seams once,
    so the depth is translated by exactly `g + h`. The total holonomy is the sum of the
    per-seam holonomies. -/
theorem holonomy_composes : ∀ (g h : ZMod 6) (x : ZMod 5 × ZMod 6),
    (K g h)^[5] x = (x.1, x.2 + (g + h)) := by decide

/-- **Summary separation.** For every `(g, h)` the systems share the identical one-step
    residue transition, yet the composite depth-holonomy `g + h` is fully recovered by
    winding the cycle once. -/
theorem two_seam_separates :
    (∀ (g h : ZMod 6) x, (K g h x).1 = x.1 + 1) ∧
    (∀ (g h : ZMod 6) x, (K g h)^[5] x = (x.1, x.2 + (g + h))) :=
  ⟨residue_marginal_indep, holonomy_composes⟩

/-- **Concrete composite order.** With `g = h = 0` the system closes after one loop. With
    `g = h = 1` the composite holonomy is `g + h = 2`, which has order `3` in `ZMod 6`, so
    the full map has order `5 · 3 = 15`: it does not close after one loop but does after
    three. Different `(g, h)` with different `g + h` yield different orbit structure. -/
theorem composite_order :
    (∀ x, (K 0 0)^[5] x = x) ∧
    (∃ x, (K 1 1)^[5] x ≠ x) ∧
    (∀ x, (K 1 1)^[15] x = x) := by decide

end Brockian.TwoSeamHolonomy
