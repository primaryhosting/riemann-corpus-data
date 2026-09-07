import Mathlib

/-! # Depth-Holonomy Separation

Two phase-depth transfer systems on the state space `ZMod 5 × ZMod 2` (residue × depth
parity) that are IDENTICAL to residue-class Fourier analysis — same one-step residue
weights, hence the same mod-5 Fourier spectrum — yet are DISTINGUISHED by a depth-holonomy
invariant that residue-Fourier data cannot see.

`K₁` carries the depth parity unchanged around the residue cycle (trivial holonomy):
`K₁⁵ = id`, so its transfer determinant factors as `det(I − zK₁) = (1 − z⁵)²` (two
5-cycles). `K₂` flips the depth parity at the seam `j = 4 → 0` (holonomy = the nontrivial
element of `ZMod 2`): `K₂⁵ ≠ id` but `K₂¹⁰ = id`, so `det(I − zK₂) = 1 − z¹⁰` (one
10-cycle). The state must wind the residue cycle *twice* to close.

The two systems are indistinguishable to residue-class (mod-5) Fourier analysis — they
share the one-step residue transition `j ↦ j + 1` — so the depth-holonomy invariant is
not a function of the residue-Fourier data. This is the finite separation showing the
branched phase-depth construction carries information beyond standard weighted-cyclic
Fourier analysis. (It establishes a new finite dynamical invariant, not an arithmetic
consequence: any bridge to prime correlations or L-function data is a separate obligation.)
-/

namespace Brockian.DepthHolonomySeparation

/-- System 1: the residue advances, the depth parity is carried unchanged.
    Depth-holonomy around the residue cycle is trivial. -/
def K₁ (x : ZMod 5 × ZMod 2) : ZMod 5 × ZMod 2 := (x.1 + 1, x.2)

/-- System 2: the residue advances, and the depth parity flips exactly when the residue
    crosses the seam `j = 4 → 0`. Depth-holonomy around the residue cycle is the nontrivial
    element of `ZMod 2`. -/
def K₂ (x : ZMod 5 × ZMod 2) : ZMod 5 × ZMod 2 :=
  (x.1 + 1, x.2 + (if x.1 = 4 then 1 else 0))

/-- Both systems induce the SAME one-step residue transition `j ↦ j + 1`; they are
    therefore identical under residue-class (mod-5) Fourier analysis. -/
theorem same_residue_weights (x : ZMod 5 × ZMod 2) : (K₁ x).1 = (K₂ x).1 := rfl

/-- System 1 has trivial depth-holonomy: five residue steps return the whole state. -/
theorem K₁_holonomy_trivial : ∀ x : ZMod 5 × ZMod 2, K₁^[5] x = x := by decide

/-- System 2 has NONTRIVIAL depth-holonomy: five residue steps do NOT return the state
    (the depth parity has flipped). -/
theorem K₂_holonomy_nontrivial : ∃ x : ZMod 5 × ZMod 2, K₂^[5] x ≠ x := by decide

/-- System 2 closes only after winding the residue cycle twice: `K₂¹⁰ = id`. -/
theorem K₂_holonomy_order_two : ∀ x : ZMod 5 × ZMod 2, K₂^[10] x = x := by decide

/-- **The separation.** Two phase-depth transfer systems with identical one-step residue
    weights (hence identical mod-5 Fourier spectra) are distinguished by their depth
    holonomy: `K₁⁵ = id` while `K₂⁵ ≠ id`. The depth-holonomy invariant is therefore not
    a function of the residue-Fourier data. -/
theorem depth_holonomy_separates :
    (∀ x, (K₁ x).1 = (K₂ x).1) ∧
    (∀ x, K₁^[5] x = x) ∧
    (∃ x, K₂^[5] x ≠ x) ∧
    (∀ x, K₂^[10] x = x) :=
  ⟨same_residue_weights, K₁_holonomy_trivial, K₂_holonomy_nontrivial, K₂_holonomy_order_two⟩

end Brockian.DepthHolonomySeparation
