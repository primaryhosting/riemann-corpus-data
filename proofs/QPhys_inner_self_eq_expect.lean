/- (header comment; Lean requires `import` to be the first command, so the header
   below is a plain block comment rather than a module docstring)
/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QPhys

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation value of a (symmetric) operator `A` in the state `psi`. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (psi : H) : ℝ := (inner ℂ psi (A psi)).re

/-- The spread (standard deviation) of `A` in the state `psi`:
`Δ A = ‖(A - ⟨A⟩) psi‖`. -/
noncomputable def spread (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  ‖A psi - ((expect A psi : ℝ) : ℂ) • psi‖

/-- For a symmetric operator, the expectation value is the full inner product (it is real). -/
lemma inner_self_eq_expect {A : H →ₗ[ℂ] H} (hA : ∀ u v : H, inner ℂ (A u) v = inner ℂ u (A v))
    (psi : H) : inner ℂ psi (A psi) = ((expect A psi : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (inner ℂ psi (A psi)) = inner ℂ psi (A psi) :=
    (inner_conj_symm (A psi) psi).trans (hA psi psi)
  have him := Complex.conj_eq_iff_im.mp h
  exact Complex.ext (by simp [expect]) (by simp [expect, him])

/-- The commutator of the shifted operators equals the commutator of the original operators,
paired against `psi`. -/
lemma inner_comm_shift {X P : H →ₗ[ℂ] H}
    (hX : ∀ u v : H, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : H, inner ℂ (P u) v = inner ℂ u (P v))
    (psi : H) (a b : ℝ) :
    inner ℂ (X psi - (a : ℂ) • psi) (P psi - (b : ℂ) • psi)
      - inner ℂ (P psi - (b : ℂ) • psi) (X psi - (a : ℂ) • psi)
      = inner ℂ psi (X (P psi) - P (X psi)) := by
  have hXs : inner ℂ (X psi) psi = inner ℂ psi (X psi) := hX psi psi
  have hPs : inner ℂ (P psi) psi = inner ℂ psi (P psi) := hP psi psi
  have hXP : inner ℂ (X psi) (P psi) = inner ℂ psi (X (P psi)) := hX psi (P psi)
  have hPX : inner ℂ (P psi) (X psi) = inner ℂ psi (P (X psi)) := hP psi (X psi)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [hXs, hPs, hXP, hPX]
  ring

/-- **Heisenberg uncertainty principle.**

Let `X` and `P` be symmetric (self-adjoint) operators on a complex inner product space
satisfying the canonical commutation relation `[X, P] psi = i ℏ psi` on a normalized
state `psi`.  Then the product of the spreads of `X` and `P` in the state `psi` is at
least `ℏ / 2`. -/
theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H}
    (hX : ∀ u v : H, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : H, inner ℂ (P u) v = inner ℂ u (P v))
    {hbar : ℝ} (hbar_nonneg : 0 ≤ hbar) {psi : H} (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    spread X psi * spread P psi ≥ hbar / 2 := by
  set a : ℝ := expect X psi with ha
  set b : ℝ := expect P psi with hb
  set u : H := X psi - (a : ℂ) • psi with hu
  set v : H := P psi - (b : ℂ) • psi with hv
  -- the commutator pairing
  have hkey : inner ℂ u v - inner ℂ v u = Complex.I * (hbar : ℂ) := by
    rw [hu, hv, inner_comm_shift hX hP psi a b, hcomm, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hpsi]
    simp
  have hconj : inner ℂ v u = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm v u).symm
  have habs : hbar = ‖inner ℂ u v - inner ℂ v u‖ := by
    rw [hkey]
    simp [abs_of_nonneg hbar_nonneg]
  have h2 : ‖inner ℂ u v - inner ℂ v u‖ ≤ 2 * ‖inner ℂ u v‖ := by
    calc ‖inner ℂ u v - inner ℂ v u‖ ≤ ‖inner ℂ u v‖ + ‖inner ℂ v u‖ := norm_sub_le _ _
      _ = 2 * ‖inner ℂ u v‖ := by rw [hconj, RCLike.norm_conj]; ring
  have h3 : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : hbar ≤ 2 * (‖u‖ * ‖v‖) := by
    calc hbar = ‖inner ℂ u v - inner ℂ v u‖ := habs
      _ ≤ 2 * ‖inner ℂ u v‖ := h2
      _ ≤ 2 * (‖u‖ * ‖v‖) := by linarith
  simp only [spread, ge_iff_le, ← ha, ← hb, ← hu, ← hv]
  linarith

end QPhys

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

