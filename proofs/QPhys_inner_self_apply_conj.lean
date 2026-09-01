/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of a symmetric operator in a state is real. -/
lemma inner_self_apply_conj (X : H →ₗ[ℂ] H) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ) :
    conj ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := by
  rw [inner_conj_symm, hX]

/-- Robertson-type identity: for symmetric `X`, `P` whose commutator acts on the unit
vector `psi` as multiplication by `i * ℏ`, the mean-shifted vectors
`u = (X - ⟨X⟩)psi`, `v = (P - ⟨P⟩)psi` satisfy `⟪u,v⟫ - ⟪v,u⟫ = i * ℏ`. -/
lemma inner_comm_sub (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (hnorm : ‖psi‖ = 1) :
    ⟪X psi - ⟪psi, X psi⟫_ℂ • psi, P psi - ⟪psi, P psi⟫_ℂ • psi⟫_ℂ
      - ⟪P psi - ⟪psi, P psi⟫_ℂ • psi, X psi - ⟪psi, X psi⟫_ℂ • psi⟫_ℂ
      = Complex.I * hbar := by
  have hself : (⟪psi, psi⟫_ℂ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have ha : conj ⟪psi, X psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := inner_self_apply_conj X psi hX
  have hb : conj ⟪psi, P psi⟫_ℂ = ⟪psi, P psi⟫_ℂ := inner_self_apply_conj P psi hP
  have hXs : ⟪X psi, psi⟫_ℂ = ⟪psi, X psi⟫_ℂ := by rw [← inner_conj_symm, ha]
  have hPs : ⟪P psi, psi⟫_ℂ = ⟪psi, P psi⟫_ℂ := by rw [← inner_conj_symm, hb]
  have hkey : ⟪X psi, P psi⟫_ℂ - ⟪P psi, X psi⟫_ℂ = Complex.I * hbar := by
    have h1 : ⟪X psi, P psi⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ := hX _ _
    have h2 : ⟪P psi, X psi⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ := hP _ _
    rw [h1, h2, ← inner_sub_right, hcomm psi, inner_smul_right, hself, mul_one]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, ha, hb,
    hXs, hPs, hself]
  rw [← hkey]
  ring

theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (hnorm : ‖psi‖ = 1) :
    ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ hbar / 2 := by
  set u : H := X psi - ⟪psi, X psi⟫_ℂ • psi with hu
  set v : H := P psi - ⟪psi, P psi⟫_ℂ • psi with hv
  have hid : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * hbar :=
    inner_comm_sub X P hbar psi hX hP hcomm hnorm
  have hconj : ⟪v, u⟫_ℂ = conj ⟪u, v⟫_ℂ := (inner_conj_symm _ _).symm
  have him : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have h2 := congrArg Complex.im hid
    rw [Complex.sub_im, hconj, Complex.conj_im] at h2
    simp [Complex.mul_im] at h2
    linarith
  calc hbar / 2 = (⟪u, v⟫_ℂ).im := him.symm
    _ ≤ ‖⟪u, v⟫_ℂ‖ := Complex.im_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _

/-- Sign-free form of the Heisenberg uncertainty relation: `Δx · Δp ≥ |ℏ| / 2`. -/
theorem heisenberg_uncertainty_abs
    (X P : H →ₗ[ℂ] H) (hbar : ℝ) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : ∀ u : H, X (P u) - P (X u) = (Complex.I * hbar) • u)
    (hnorm : ‖psi‖ = 1) :
    ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ |hbar| / 2 := by
  have h₁ : ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ * ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ ≥ hbar / 2 :=
    heisenberg_uncertainty X P hbar psi hX hP hcomm hnorm
  have hcomm' : ∀ u : H, P (X u) - X (P u) = (Complex.I * (-hbar : ℝ)) • u := by
    intro u
    have h := hcomm u
    have hneg : (Complex.I * ((-hbar : ℝ) : ℂ)) • u = -((Complex.I * (hbar : ℂ)) • u) := by
      rw [← neg_smul]
      push_cast
      ring_nf
    rw [hneg, ← h]
    abel
  have h₂ : ‖P psi - ⟪psi, P psi⟫_ℂ • psi‖ * ‖X psi - ⟪psi, X psi⟫_ℂ • psi‖ ≥ (-hbar) / 2 :=
    heisenberg_uncertainty P X (-hbar) psi hP hX hcomm' hnorm
  rcases abs_cases hbar with ⟨h, _⟩ | ⟨h, _⟩
  · rw [ge_iff_le, h]; exact h₁
  · rw [ge_iff_le, h, mul_comm]; exact h₂

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

