import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any comment, so the header block above sits
directly after the single `import Mathlib` line.)
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

set_option grind.warning false

namespace QI

open Matrix Complex

/-- Amplitudes of a pure state of three qubits `A`, `B`, `C`:
`ψ i j k` is the coefficient of the computational basis vector `|i j k⟩`. -/
abbrev Amp : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`, i.e. `Tr_{BC} |ψ⟩⟨ψ|`. -/
noncomputable def rhoA (ψ : Amp) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i i' => ∑ j, ∑ k, ψ i j k * (starRingEnd ℂ) (ψ i' j k)

/-- The reduced density matrix of the pair `AB`, i.e. `Tr_C |ψ⟩⟨ψ|`.
Rows and columns are indexed by the pair of basis labels of `A` and `B`. -/
noncomputable def rhoAB (ψ : Amp) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => ∑ k, ψ p.1 p.2 k * (starRingEnd ℂ) (ψ q.1 q.2 k)

/-- The reduced density matrix of the pair `AC`, i.e. `Tr_B |ψ⟩⟨ψ|`.
Rows and columns are indexed by the pair of basis labels of `A` and `C`. -/
noncomputable def rhoAC (ψ : Amp) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => ∑ j, ψ p.1 j p.2 * (starRingEnd ℂ) (ψ q.1 j q.2)

/-- The Pauli matrix `σ_y`. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The two-qubit spin-flip operator `σ_y ⊗ σ_y`. -/
def YY : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => sigmaY p.1 q.1 * sigmaY p.2 q.2

/-- The Wootters spin flip `ρ ↦ ρ̃ = (σ_y ⊗ σ_y) ρ* (σ_y ⊗ σ_y)` of a two-qubit density matrix,
where `ρ*` is the entrywise complex conjugate in the computational basis. -/
noncomputable def spinFlip (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  YY * ρ.map (starRingEnd ℂ) * YY

/-- The squared Wootters concurrence of a two-qubit density matrix of rank at most two.

Wootters' concurrence is `C(ρ) = max (0, √λ₁ - √λ₂ - √λ₃ - √λ₄)`, where the `λᵢ` are the
(real, nonnegative) eigenvalues of `M = ρ ρ̃` in decreasing order.  When `ρ` has rank at most
two — which is the case for the two-party marginals of a pure three-qubit state — one has
`λ₃ = λ₄ = 0`, hence
`C(ρ)² = (√λ₁ - √λ₂)² = (λ₁ + λ₂) - 2√(λ₁λ₂) = tr M - 2√(e₂ M)`,
where `e₂ M = (tr M ^ 2 - tr (M ^ 2)) / 2` is the second elementary symmetric function of the
eigenvalues of `M`.  This is the formula used as the definition here. -/
noncomputable def concurrenceSq (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  ((ρ * spinFlip ρ).trace).re -
    2 * Real.sqrt
      ((((ρ * spinFlip ρ).trace ^ 2 - ((ρ * spinFlip ρ) * (ρ * spinFlip ρ)).trace) / 2).re)

/-- Justification of the definition of `concurrenceSq`: if the matrix `M = ρ ρ̃` has spectrum
`{l₁, l₂, 0, 0}` with `0 ≤ l₂ ≤ l₁` (so that `tr M = l₁ + l₂` and `e₂ M = l₁ l₂`), then
`concurrenceSq ρ` is exactly Wootters' `(√l₁ - √l₂ - √0 - √0)²`. -/
theorem concurrenceSq_eq_wootters (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (l₁ l₂ : ℝ)
    (hl₂ : 0 ≤ l₂) (hl : l₂ ≤ l₁)
    (htr : (ρ * spinFlip ρ).trace = ((l₁ + l₂ : ℝ) : ℂ))
    (he₂ : ((ρ * spinFlip ρ).trace ^ 2 - ((ρ * spinFlip ρ) * (ρ * spinFlip ρ)).trace) / 2
      = ((l₁ * l₂ : ℝ) : ℂ)) :
    concurrenceSq ρ = (Real.sqrt l₁ - Real.sqrt l₂) ^ 2 := by
  have hl₁ : 0 ≤ l₁ := le_trans hl₂ hl
  simp only [concurrenceSq]
  rw [he₂, htr]
  simp only [Complex.ofReal_re]
  rw [Real.sqrt_mul hl₁]
  have e₁ : Real.sqrt l₁ ^ 2 = l₁ := Real.sq_sqrt hl₁
  have e₂ : Real.sqrt l₂ ^ 2 = l₂ := Real.sq_sqrt hl₂
  linear_combination -e₁ - e₂

/-- The tangle of qubit `A` against the pair `BC`, `τ_{A(BC)} = 4 det ρ_A`,
which is the squared concurrence of the pure-state bipartite cut `A | BC`. -/
noncomputable def tangleA (ψ : Amp) : ℝ := 4 * ((rhoA ψ).det).re

/-- Key algebraic identity: for a pure three-qubit state,
`tr (ρ_AB ρ̃_AB) + tr (ρ_AC ρ̃_AC) = 4 det ρ_A`. -/
theorem trace_spinFlip_add_trace_spinFlip (ψ : Amp) :
    (rhoAB ψ * spinFlip (rhoAB ψ)).trace + (rhoAC ψ * spinFlip (rhoAC ψ)).trace
      = 4 * (rhoA ψ).det := by
  simp [rhoAB, rhoAC, rhoA, spinFlip, YY, sigmaY, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.det_fin_two, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring_nf

theorem monogamy_ckw (ψ : Amp) :
    concurrenceSq (rhoAB ψ) + concurrenceSq (rhoAC ψ) ≤ tangleA ψ := by
  have key : (rhoAB ψ * spinFlip (rhoAB ψ)).trace.re + (rhoAC ψ * spinFlip (rhoAC ψ)).trace.re
      = 4 * ((rhoA ψ).det).re := by
    rw [← Complex.add_re, trace_spinFlip_add_trace_spinFlip]
    simp [Complex.mul_re]
  have h1 : (0:ℝ) ≤ Real.sqrt
      (((((rhoAB ψ) * spinFlip (rhoAB ψ)).trace ^ 2
        - (((rhoAB ψ) * spinFlip (rhoAB ψ)) * ((rhoAB ψ) * spinFlip (rhoAB ψ))).trace) / 2).re) :=
    Real.sqrt_nonneg _
  have h2 : (0:ℝ) ≤ Real.sqrt
      (((((rhoAC ψ) * spinFlip (rhoAC ψ)).trace ^ 2
        - (((rhoAC ψ) * spinFlip (rhoAC ψ)) * ((rhoAC ψ) * spinFlip (rhoAC ψ))).trace) / 2).re) :=
    Real.sqrt_nonneg _
  simp only [concurrenceSq, tangleA]
  linarith [key, h1, h2]

/-! ### Sanity checks on the two archetypal three-qubit states

Both states are taken unnormalised (all nonzero amplitudes equal to `1`); every quantity below is
homogeneous of degree four in the amplitudes, so this only rescales the values.
For `GHZ` the inequality is strict (residual three-tangle `4`), for `W` it is an equality. -/

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
def ghz : Amp := fun i j k => if i = j ∧ j = k then 1 else 0

/-- The (unnormalised) W state `|001⟩ + |010⟩ + |100⟩`. -/
def wState : Amp := fun i j k => if (i : ℕ) + (j : ℕ) + (k : ℕ) = 1 then 1 else 0

example : tangleA ghz = 4 := by
  simp [tangleA, ghz, rhoA, Fin.sum_univ_two, Matrix.det_fin_two]

example : concurrenceSq (rhoAB ghz) = 0 := by
  simp [concurrenceSq, spinFlip, YY, sigmaY, rhoAB, ghz, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

example : tangleA wState = 8 := by
  simp [tangleA, wState, rhoA, Fin.sum_univ_two, Matrix.det_fin_two]
  norm_num

example : concurrenceSq (rhoAB wState) = 4 := by
  simp [concurrenceSq, spinFlip, YY, sigmaY, rhoAB, wState, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end QI

