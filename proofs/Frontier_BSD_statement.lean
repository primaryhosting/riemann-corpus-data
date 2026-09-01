import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Overview

We formalise the statement of the Birch–Swinnerton-Dyer conjecture (rank part) for an
elliptic curve over `ℚ`, given by a minimal integral Weierstrass model `E`:

  `ord_{s=1} L(E, s) = rank E(ℚ)`.

* The *analytic* side is the order of vanishing at `s = 1` of any entire function `L`
  which agrees with the Dirichlet series `∑ a_n n^{-s}` on the half plane `Re s > 3/2`
  (where that series converges); the coefficients `a_n` are built from the point counts
  of the reductions `E mod p` in the usual way.
* The *algebraic* side is the Mordell–Weil rank, i.e. the `ℚ`-dimension of
  `ℚ ⊗_ℤ E(ℚ)`.

The statement is well posed: by the identity theorem, an entire continuation of the
Dirichlet series is unique (`Frontier.LFunction_unique`), so the analytic order of
vanishing does not depend on the choice of `L`
(`Frontier.analyticOrder_eq_of_isLFunction`).

The target theorem `Frontier.BSD_statement` is a Lean-checked reduction: assuming the
conjecture, we derive the classical rank-zero criterion
`L(E, 1) ≠ 0 ↔ rank E(ℚ) = 0`.
-/

namespace Frontier

open WeierstrassCurve

/-- The trace of Frobenius at `p` for the integral Weierstrass model `E`, defined as
`a_p = p + 1 - #E_ns(𝔽_p)`, where `E_ns(𝔽_p)` is the group of nonsingular points of the
reduction of `E` modulo `p` (this is the usual `a_p` for good primes, and gives
`1`, `-1`, `0` at primes of split multiplicative, nonsplit multiplicative and additive
reduction respectively, provided the model is minimal). -/
noncomputable def apCoeff (E : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (Nat.card ((E.map (Int.castRingHom (ZMod p))).toAffine.Point) : ℤ)

/-- The coefficient `a_{p^k}` of the `L`-series of `E`, given by the usual recursion
`a_{p^{k+2}} = a_p a_{p^{k+1}} - p·a_{p^k}` at primes of good reduction (`p ∤ Δ`), and by
`a_{p^{k+1}} = a_p a_{p^k}` at primes of bad reduction (`p ∣ Δ`). -/
noncomputable def aPrimePow (E : WeierstrassCurve ℤ) (p : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => apCoeff E p
  | (k + 2) =>
      apCoeff E p * aPrimePow E p (k + 1)
        - (if (p : ℤ) ∣ E.Δ then 0 else (p : ℤ)) * aPrimePow E p k

/-- The `n`-th coefficient of the `L`-series of `E`, the multiplicative extension of the
coefficients `a_{p^k}`. -/
noncomputable def anCoeff (E : WeierstrassCurve ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, aPrimePow E p (n.factorization p)

/-- The Dirichlet series `∑ a_n n^{-s}` attached to `E`; it converges for `Re s > 3/2`
and the `L`-function of `E` is its analytic continuation. -/
noncomputable def LSeriesOf (E : WeierstrassCurve ℤ) : ℂ → ℂ :=
  LSeries (fun n : ℕ => (anCoeff E n : ℂ))

/-- `L` is *the* `L`-function of `E`: it is entire, and on the half plane of absolute
convergence `Re s > 3/2` it is given by the Dirichlet series `∑ a_n n^{-s}`. -/
def IsLFunction (E : WeierstrassCurve ℤ) (L : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ L Set.univ ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = LSeriesOf E s

/-- `E` is a minimal integral Weierstrass model: among all integral models of the same
elliptic curve over `ℚ` (i.e. those becoming isomorphic to `E` over `ℚ` after a change of
variables) it has discriminant of smallest absolute value. -/
def IsMinimalModel (E : WeierstrassCurve ℤ) : Prop :=
  ∀ E' : WeierstrassCurve ℤ,
    (∃ u : WeierstrassCurve.VariableChange ℚ,
      u • (E'.map (Int.castRingHom ℚ)) = E.map (Int.castRingHom ℚ)) →
    E.Δ.natAbs ≤ E'.Δ.natAbs

/-- The Mordell–Weil rank of `E(ℚ)`: the `ℚ`-dimension of `ℚ ⊗_ℤ E(ℚ)`. -/
noncomputable def mordellWeilRank (E : WeierstrassCurve ℤ) : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ ((E.map (Int.castRingHom ℚ)).toAffine.Point))

/-- **The Birch and Swinnerton-Dyer conjecture (rank part).** For every elliptic curve
over `ℚ`, given by a minimal integral Weierstrass model `E` with nonzero discriminant, the
order of vanishing at `s = 1` of the `L`-function of `E` equals the Mordell–Weil rank of
`E(ℚ)`. -/
def BSD_conjecture : Prop :=
  ∀ E : WeierstrassCurve ℤ, E.Δ ≠ 0 → IsMinimalModel E →
    ∀ L : ℂ → ℂ, IsLFunction E L → analyticOrderAt L 1 = (mordellWeilRank E : ℕ∞)

/-- The half plane of absolute convergence is open. -/
lemma isOpen_halfPlane : IsOpen {s : ℂ | 3 / 2 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- **Well-posedness.** The `L`-function of `E` is unique: two entire functions agreeing
with the Dirichlet series of `E` on `Re s > 3/2` are equal, by the identity theorem. -/
theorem LFunction_unique (E : WeierstrassCurve ℤ) (L₁ L₂ : ℂ → ℂ)
    (h₁ : IsLFunction E L₁) (h₂ : IsLFunction E L₂) : L₁ = L₂ := by
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hev : L₁ =ᶠ[nhds (2 : ℂ)] L₂ := by
    filter_upwards [isOpen_halfPlane.mem_nhds hmem] with s hs
    rw [h₁.2 s hs, h₂.2 s hs]
  have := h₁.1.eqOn_of_preconnected_of_eventuallyEq h₂.1 isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  funext s
  exact this (Set.mem_univ s)

/-- Consequently the analytic order of vanishing at `s = 1` does not depend on the choice
of the analytic continuation. -/
theorem analyticOrder_eq_of_isLFunction (E : WeierstrassCurve ℤ) (L₁ L₂ : ℂ → ℂ)
    (h₁ : IsLFunction E L₁) (h₂ : IsLFunction E L₂) :
    analyticOrderAt L₁ 1 = analyticOrderAt L₂ 1 := by
  rw [LFunction_unique E L₁ L₂ h₁ h₂]

/-- **Target: a Lean-checked reduction of BSD.** Assuming the Birch–Swinnerton-Dyer
conjecture, for a minimal integral model `E` of an elliptic curve over `ℚ` and its
`L`-function `L`, the Mordell–Weil rank of `E(ℚ)` vanishes exactly when `L(E, 1) ≠ 0`
(the rank-zero, i.e. "base", case of the conjecture). -/
theorem BSD_statement (hBSD : BSD_conjecture) (E : WeierstrassCurve ℤ) (hΔ : E.Δ ≠ 0)
    (hmin : IsMinimalModel E) (L : ℂ → ℂ) (hL : IsLFunction E L) :
    L 1 ≠ 0 ↔ mordellWeilRank E = 0 := by
  have hord : analyticOrderAt L 1 = (mordellWeilRank E : ℕ∞) := hBSD E hΔ hmin L hL
  have hana : AnalyticAt ℂ L 1 := hL.1 (1 : ℂ) (Set.mem_univ _)
  constructor
  · intro hne
    have : analyticOrderAt L 1 = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord] at this
    exact_mod_cast this
  · intro hrank
    rw [hrank] at hord
    have : ¬ AnalyticAt ℂ L 1 ∨ L 1 ≠ 0 := analyticOrderAt_eq_zero.1 (by exact_mod_cast hord)
    rcases this with h | h
    · exact absurd hana h
    · exact h

end Frontier

