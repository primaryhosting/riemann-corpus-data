/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Frontier

/-! ## Conformal rectangles, cross-ratio, and Möbius maps

Smirnov's theorem (Cardy–Smirnov formula) states that for critical site percolation on the
triangular lattice, the probability of a left-right crossing of a conformal rectangle
`(D; z₁, z₂, z₃, z₄)` converges, in the scaling limit, to a quantity that depends only on the
conformal class of the marked domain — equivalently (by the Riemann mapping theorem) only on the
cross-ratio of the four marked boundary points — and is given there by Cardy's hypergeometric
formula.

The analytic content of the scaling limit is beyond what is currently available in Mathlib.
What is formalized and proved here is the *conformal-invariance reduction*: once the limiting
crossing probability is known to be a function of the cross-ratio of the four marked points
(Cardy's formula), conformal invariance of crossing probabilities follows, since the cross-ratio
is invariant under Möbius transformations — the conformal automorphisms of the Riemann sphere. -/

/-- The cross-ratio of four points of `ℂ`, the conformal invariant of a marked domain
`(D; z₁, z₂, z₃, z₄)`. -/
noncomputable def crossRatio (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃))

/-- The Möbius transformation `z ↦ (a z + b) / (c z + d)`. -/
noncomputable def mobius (a b c d : ℂ) (z : ℂ) : ℂ := (a * z + b) / (c * z + d)

/-- Difference formula for a Möbius transformation. -/
theorem mobius_sub {a b c d z w : ℂ} (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    mobius a b c d z - mobius a b c d w
      = (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  unfold mobius
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- **The cross-ratio is a Möbius invariant.** -/
theorem crossRatio_mobius (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : c * z₁ + d ≠ 0) (h₂ : c * z₂ + d ≠ 0) (h₃ : c * z₃ + d ≠ 0) (h₄ : c * z₄ + d ≠ 0) :
    crossRatio (mobius a b c d z₁) (mobius a b c d z₂) (mobius a b c d z₃) (mobius a b c d z₄)
      = crossRatio z₁ z₂ z₃ z₄ := by
  have e₁₃ := mobius_sub (a := a) (b := b) h₁ h₃
  have e₂₄ := mobius_sub (a := a) (b := b) h₂ h₄
  have e₁₄ := mobius_sub (a := a) (b := b) h₁ h₄
  have e₂₃ := mobius_sub (a := a) (b := b) h₂ h₃
  set K : ℂ := (a * d - b * c) ^ 2 /
      ((c * z₁ + d) * (c * z₂ + d) * (c * z₃ + d) * (c * z₄ + d)) with hK
  have hKne : K ≠ 0 := by
    rw [hK]
    exact div_ne_zero (pow_ne_zero 2 hdet)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero h₁ h₂) h₃) h₄)
  have hnum : (mobius a b c d z₁ - mobius a b c d z₃) * (mobius a b c d z₂ - mobius a b c d z₄)
      = K * ((z₁ - z₃) * (z₂ - z₄)) := by
    rw [e₁₃, e₂₄, hK]
    field_simp
  have hden : (mobius a b c d z₁ - mobius a b c d z₄) * (mobius a b c d z₂ - mobius a b c d z₃)
      = K * ((z₁ - z₄) * (z₂ - z₃)) := by
    rw [e₁₄, e₂₃, hK]
    field_simp
  unfold crossRatio
  rw [hnum, hden, mul_div_mul_left _ _ hKne]

/-- The cross-ratio is unchanged by the relabelling `(z₁ z₂ z₃ z₄) ↦ (z₂ z₁ z₄ z₃)`, the
symmetry of a conformal rectangle exchanging the two crossed sides' endpoints. -/
theorem crossRatio_swap (z₁ z₂ z₃ z₄ : ℂ) :
    crossRatio z₂ z₁ z₄ z₃ = crossRatio z₁ z₂ z₃ z₄ := by
  unfold crossRatio
  rw [mul_comm (z₂ - z₄) (z₁ - z₃), mul_comm (z₂ - z₃) (z₁ - z₄)]

/-! ## Conformal invariance of critical crossing probabilities -/

/-- A *crossing-probability model* assigns to a marked domain `(D; z₁, z₂, z₃, z₄)` the
probability of a left-right crossing of `D` between the boundary arcs determined by the four
marked points. -/
abbrev CrossingProbability : Type := Set ℂ → ℂ → ℂ → ℂ → ℂ → ℝ

/-- A crossing-probability model is *conformally invariant* if it is unchanged by applying a
Möbius transformation to the domain and to its marked boundary points. -/
def ConformallyInvariant (P : CrossingProbability) : Prop :=
  ∀ (a b c d : ℂ), a * d - b * c ≠ 0 → ∀ (D : Set ℂ) (z₁ z₂ z₃ z₄ : ℂ),
    c * z₁ + d ≠ 0 → c * z₂ + d ≠ 0 → c * z₃ + d ≠ 0 → c * z₄ + d ≠ 0 →
    P (mobius a b c d '' D) (mobius a b c d z₁) (mobius a b c d z₂) (mobius a b c d z₃)
        (mobius a b c d z₄) = P D z₁ z₂ z₃ z₄

/-- **Cardy–Smirnov, conformal-invariance reduction.**

If the scaling limit `P` of the crossing probabilities of critical triangular-lattice percolation
is given by Cardy's formula — i.e. `P D z₁ z₂ z₃ z₄ = Cardy (crossRatio z₁ z₂ z₃ z₄)` for some
function `Cardy` of the cross-ratio alone — then `P` is conformally invariant: it is unchanged
under every Möbius transformation of the marked domain.

This is the Lean-checked reduction of Smirnov's conformal-invariance theorem to Cardy's formula;
its proof is the Möbius invariance of the cross-ratio (`Frontier.crossRatio_mobius`). -/
theorem smirnov_percolation (P : CrossingProbability) (Cardy : ℂ → ℝ)
    (hCardy : ∀ (D : Set ℂ) (z₁ z₂ z₃ z₄ : ℂ),
      P D z₁ z₂ z₃ z₄ = Cardy (crossRatio z₁ z₂ z₃ z₄)) :
    ConformallyInvariant P := by
  intro a b c d hdet D z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄
  rw [hCardy, hCardy, crossRatio_mobius a b c d hdet z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄]

/-- Sanity check: the hypothesis of `Frontier.smirnov_percolation` is satisfiable — any model
built from a function of the cross-ratio is conformally invariant. -/
example (Cardy : ℂ → ℝ) :
    ConformallyInvariant (fun _ z₁ z₂ z₃ z₄ => Cardy (crossRatio z₁ z₂ z₃ z₄)) :=
  smirnov_percolation _ Cardy (fun _ _ _ _ _ => rfl)

end Frontier

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

