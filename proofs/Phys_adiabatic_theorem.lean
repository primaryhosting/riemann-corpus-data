import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

namespace Phys

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The **Kato generator** of the adiabatic evolution associated with a differentiable family
`P` of spectral projections, with derivative `dP`:  `K s = P' s P s - P s P' s`. -/
noncomputable def katoGen (P dP : ℝ → (H →L[ℂ] H)) (s : ℝ) : H →L[ℂ] H :=
  dP s * P s - P s * dP s

/-- Pure algebra: if `p` is idempotent and `q = q p + p q` (the derivative relation obtained by
differentiating `P² = P`), then the commutator of the Kato generator `k = q p - p q` with `p`
reproduces `q`, i.e. `k p - p k = q`. -/
theorem kato_commutator {A : Type*} [Ring A] (p q : A) (hp : p * p = p)
    (hq : q = q * p + p * q) :
    (q * p - p * q) * p - p * (q * p - p * q) = q := by
  have hpqp : p * q * p = 0 := by
    have h : p * q = p * q * p + p * q := by
      calc p * q = p * (q * p + p * q) := by rw [← hq]
        _ = p * q * p + p * p * q := by noncomm_ring
        _ = p * q * p + p * q := by rw [hp]
    have h' : p * q * p + p * q = 0 + p * q := by rw [zero_add]; exact h.symm
    exact add_right_cancel h'
  have e1 : (q * p - p * q) * p - p * (q * p - p * q)
      = q * (p * p) - p * q * p - p * q * p + (p * p) * q := by noncomm_ring
  rw [e1, hp, hpqp, sub_zero, sub_zero]
  exact hq.symm

/-- Differentiating the idempotency relation `P s ^ 2 = P s`. -/
theorem deriv_of_idempotent (P dP : ℝ → (H →L[ℂ] H))
    (hproj : ∀ s, P s * P s = P s) (hP : ∀ s, HasDerivAt P (dP s) s) (s : ℝ) :
    dP s = dP s * P s + P s * dP s := by
  have h1 : HasDerivAt (fun t => P t * P t) (dP s * P s + P s * dP s) s :=
    (hP s).mul (hP s)
  have h2 : HasDerivAt (fun t => P t * P t) (dP s) s := by
    simpa only [hproj] using hP s
  exact (h2.unique h1)

/-- The key differential identity: `P' s = K s P s - P s K s` for the Kato generator `K`. -/
theorem katoGen_commutator (P dP : ℝ → (H →L[ℂ] H))
    (hproj : ∀ s, P s * P s = P s) (hP : ∀ s, HasDerivAt P (dP s) s) (s : ℝ) :
    katoGen P dP s * P s - P s * katoGen P dP s = dP s :=
  kato_commutator (P s) (dP s) (hproj s) (deriv_of_idempotent P dP hproj hP s)

/-- **Kato's intertwining property.**  If `U` solves the adiabatic equation
`U' = K U` with `U 0 = 1`, where `K` is the Kato generator of the family of spectral
projections `P`, then `U` maps the initial eigenspace exactly onto the instantaneous one:
`P s ∘ U s = U s ∘ P 0`. -/
theorem kato_intertwining (P dP U : ℝ → (H →L[ℂ] H))
    (hproj : ∀ s, P s * P s = P s) (hP : ∀ s, HasDerivAt P (dP s) s)
    (hdP : Continuous dP)
    (hU : ∀ s, HasDerivAt U (katoGen P dP s * U s) s) (hU0 : U 0 = 1)
    {s : ℝ} (hs : 0 ≤ s) :
    P s * U s = U s * P 0 := by
  set K : ℝ → (H →L[ℂ] H) := katoGen P dP
  set A : ℝ → (H →L[ℂ] H) := fun t => P t * U t - U t * P 0 with hA
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hKc : Continuous K := (hdP.mul hPc).sub (hPc.mul hdP)
  -- the difference `A` solves the same linear ODE `A' = K A`
  have hA' : ∀ t : ℝ, HasDerivAt A (K t * A t) t := by
    intro t
    have h1 : HasDerivAt (fun r => P r * U r) (dP t * U t + P t * (K t * U t)) t :=
      (hP t).mul (hU t)
    have h2 : HasDerivAt (fun r => U r * P 0) ((K t * U t) * P 0) t :=
      (hU t).mul_const (P 0)
    have h3 : HasDerivAt A (dP t * U t + P t * (K t * U t) - (K t * U t) * P 0) t := h1.sub h2
    have hcomm : K t * P t - P t * K t = dP t := katoGen_commutator P dP hproj hP t
    have : dP t * U t + P t * (K t * U t) - (K t * U t) * P 0 = K t * A t := by
      have : dP t * U t + P t * (K t * U t) = (K t * P t) * U t := by
        rw [← hcomm]; noncomm_ring
      rw [hA]
      simp only
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← this]
      noncomm_ring
    exact this ▸ h3
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun t => (hA' t).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn
    hKc.continuousOn
  have hA0 : A 0 = 0 := by
    simp [hA, hU0]
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) s, ‖K x * A x‖ ≤ M * ‖A x‖ + 0 := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) s := Set.mem_Icc.2 ⟨hx.1, le_of_lt hx.2⟩
    calc ‖K x * A x‖ ≤ ‖K x‖ * ‖A x‖ := norm_mul_le _ _
      _ ≤ M * ‖A x‖ := by
          exact mul_le_mul_of_nonneg_right (hM x hx') (norm_nonneg _)
      _ = M * ‖A x‖ + 0 := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := A) (f' := fun t => K t * A t)
    (δ := 0) (K := M) (ε := 0) (a := 0) (b := s) hAc.continuousOn
    (fun x _ => (hA' x).hasDerivWithinAt) (by simp [hA0]) hbound s (Set.mem_Icc.2 ⟨hs, le_refl s⟩)
  have hzero : A s = 0 := by
    have : ‖A s‖ ≤ 0 := by
      simpa [gronwallBound] using hgr
    exact norm_le_zero_iff.1 this
  simpa [hA, sub_eq_zero] using hzero

/-- **Adiabatic theorem (Kato).**
`Ham` is a family of Hamiltonians with a nondegenerate instantaneous eigenvalue `E s`, whose
(rank-one) spectral projection is `P s`, with eigenvector `evec s`; `dP` is the derivative of the
slowly varying family `P`, and `U` is the associated adiabatic evolution, i.e. the solution of
`U' = K U`, `U 0 = 1`, generated by the Kato generator `K = P' P - P P'`.

Then a state `ψ₀` initially in the eigenspace of `E 0` is carried by the adiabatic evolution into
the instantaneous eigenspace at every later time: `U s ψ₀` lies on the line spanned by `evec s` and
is an eigenvector of `Ham s` with eigenvalue `E s`. -/
theorem adiabatic_theorem (Ham P dP U : ℝ → (H →L[ℂ] H)) (Eig : ℝ → ℂ) (evec : ℝ → H) (ψ₀ : H)
    (hproj : ∀ s, P s * P s = P s) (hP : ∀ s, HasDerivAt P (dP s) s)
    (hdP : Continuous dP)
    (heig : ∀ s, Ham s * P s = Eig s • P s)
    (hnondeg : ∀ s, LinearMap.range (P s : H →ₗ[ℂ] H) = Submodule.span ℂ {evec s})
    (hU : ∀ s, HasDerivAt U (katoGen P dP s * U s) s) (hU0 : U 0 = 1)
    (hψ₀ : P 0 ψ₀ = ψ₀) {s : ℝ} (hs : 0 ≤ s) :
    Ham s (U s ψ₀) = Eig s • U s ψ₀ ∧ U s ψ₀ ∈ Submodule.span ℂ {evec s} := by
  have key : P s (U s ψ₀) = U s ψ₀ := by
    have h := congrArg (fun T : H →L[ℂ] H => T ψ₀) (kato_intertwining P dP U hproj hP hdP hU hU0 hs)
    simpa [hψ₀] using h
  constructor
  · have := congrArg (fun T : H →L[ℂ] H => T (U s ψ₀)) (heig s)
    simpa [key] using this
  · rw [← hnondeg s, ← key]
    exact ⟨U s ψ₀, rfl⟩

/-- Non-vacuity check: the hypothesis bundle of `Phys.adiabatic_theorem` is satisfiable with a
nonzero initial state. -/
theorem adiabatic_hypotheses_satisfiable :
    ∃ (Ham P dP U : ℝ → (ℂ →L[ℂ] ℂ)) (Eig : ℝ → ℂ) (evec : ℝ → ℂ) (ψ₀ : ℂ),
      (∀ s, P s * P s = P s) ∧ (∀ s, HasDerivAt P (dP s) s) ∧ Continuous dP ∧
      (∀ s, Ham s * P s = Eig s • P s) ∧
      (∀ s, LinearMap.range (P s : ℂ →ₗ[ℂ] ℂ) = Submodule.span ℂ {evec s}) ∧
      (∀ s, HasDerivAt U (katoGen P dP s * U s) s) ∧ U 0 = 1 ∧ P 0 ψ₀ = ψ₀ ∧ ψ₀ ≠ 0 := by
  refine ⟨fun s => (s : ℂ) • 1, fun _ => 1, fun _ => 0, fun _ => 1, fun s => (s : ℂ),
    fun _ => 1, 1, fun s => by simp, fun s => hasDerivAt_const _ _, continuous_const,
    fun s => by simp, fun s => ?_, fun s => ?_, rfl, by simp, one_ne_zero⟩
  · ext x
    simp only [LinearMap.mem_range, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, by simp⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, by simp⟩
  · simpa [katoGen] using hasDerivAt_const s (1 : ℂ →L[ℂ] ℂ)

end Phys

