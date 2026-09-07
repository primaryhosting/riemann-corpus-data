import Mathlib

/-!
# A finite-model "Riemann hypothesis" for the phase-depth transfer operator

The transfer operator of a permutation `σ` of a finite set `X` is its permutation matrix
`P = (Equiv.toPEquiv σ).toMatrix` (here over `ℂ`).  Its dynamical zeta is `det(1 − z • P)`
and its "spectrum" is the set of eigenvalues of `P`.

Because `P` is a permutation matrix it has finite multiplicative order:
`P ^ (orderOf σ) = 1`.  Consequently every eigenvalue `μ` of `P` satisfies
`μ ^ (orderOf σ) = 1` — a root of unity — hence `‖μ‖ = 1`.  Dually, every zero `z ≠ 0` of
the finite zeta `det(1 − z • P)` is the reciprocal of an eigenvalue, so `‖z‖ = 1`:

> **all zeros of the finite dynamical zeta lie on the unit circle `|z| = 1`** — the honest
> finite analogue of "all zeros on the critical line".

This is finite spectral geometry, provably true; it is **not** the Riemann hypothesis.

Everything is AXLE-clean at env `lean-4.32.2`: no `sorry`/`admit`/`native_decide`/`axiom`;
the only axioms used are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Brockian.PhaseDepthFiniteRH

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The transfer operator as a permutation matrix over `ℂ` -/

/-- The **transfer operator** of a permutation `σ`: its permutation matrix over `ℂ`. -/
noncomputable def transferMatrix (σ : Equiv.Perm X) : Matrix X X ℂ :=
  σ.toPEquiv.toMatrix

/-- Powers of the transfer matrix are the permutation matrices of the powers of `σ`.
`σ ↦ σ.toPEquiv.toMatrix` sends composition to matrix multiplication
(`PEquiv.toMatrix_trans`), so it sends `σ ^ n` to `(transferMatrix σ) ^ n`. -/
lemma transferMatrix_pow (σ : Equiv.Perm X) (n : ℕ) :
    (transferMatrix σ) ^ n = (σ ^ n).toPEquiv.toMatrix := by
  unfold transferMatrix
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Equiv.Perm.one_def, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  | succ k ih =>
    rw [pow_succ, ih, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
        ← Equiv.Perm.mul_def, ← pow_succ']

/-- **Target 1 — the transfer matrix has finite multiplicative order.**
`P ^ (orderOf σ) = 1`, because `σ ^ (orderOf σ) = 1` and the permutation matrix of the
identity is the identity matrix. -/
theorem transferMatrix_pow_orderOf_eq_one (σ : Equiv.Perm X) :
    (transferMatrix σ) ^ (orderOf σ) = 1 := by
  rw [transferMatrix_pow, pow_orderOf_eq_one, Equiv.Perm.one_def, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

/-! ## Eigenvalues of the transfer operator -/

/-- `μ` is an **eigenvalue** of the transfer operator `P = transferMatrix σ` if some nonzero
vector `v` satisfies `P *ᵥ v = μ • v`. -/
def HasEigenvalue (σ : Equiv.Perm X) (μ : ℂ) : Prop :=
  ∃ v : X → ℂ, v ≠ 0 ∧ (transferMatrix σ).mulVec v = μ • v

/-- An eigenvector of `P` for `μ` is an eigenvector of `P ^ n` for `μ ^ n`. -/
lemma transferMatrix_pow_mulVec (σ : Equiv.Perm X) {μ : ℂ} {v : X → ℂ}
    (hv : (transferMatrix σ).mulVec v = μ • v) (n : ℕ) :
    ((transferMatrix σ) ^ n).mulVec v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul,
        ← pow_succ]

/-- **Target 2a — every eigenvalue is a root of unity.**
If `μ` is an eigenvalue of `P = transferMatrix σ` then `μ ^ (orderOf σ) = 1`. -/
theorem eigenvalue_pow_orderOf (σ : Equiv.Perm X) {μ : ℂ} (h : HasEigenvalue σ μ) :
    μ ^ (orderOf σ) = 1 := by
  obtain ⟨v, hv0, hv⟩ := h
  have hpow := transferMatrix_pow_mulVec σ hv (orderOf σ)
  rw [transferMatrix_pow_orderOf_eq_one, Matrix.one_mulVec] at hpow
  -- hpow : v = μ ^ (orderOf σ) • v
  have hz : (μ ^ orderOf σ - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hpow, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h1
  · rwa [sub_eq_zero] at h1
  · exact absurd h1 hv0

/-- **Target 2b — every eigenvalue lies on the unit circle.**
If `μ` is an eigenvalue of `P = transferMatrix σ` then `‖μ‖ = 1`.
This is the finite RH in *eigenvalue form*: the whole spectrum of the transfer operator
sits on `|μ| = 1`. -/
theorem eigenvalue_norm_eq_one (σ : Equiv.Perm X) {μ : ℂ} (h : HasEigenvalue σ μ) :
    ‖μ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (eigenvalue_pow_orderOf σ h) (orderOf_pos σ).ne'

/-! ## The determinant-zero bridge and the headline -/

/-- **Target 3 — the finite Riemann hypothesis (zeta-zero form).**
Every zero `z ≠ 0` of the finite dynamical zeta `z ↦ det(1 − z • P)` lies on the unit
circle `|z| = 1`.

Proof: a zero of the determinant produces a nonzero kernel vector `v` of `1 − z • P`, i.e.
`v = z • (P *ᵥ v)`; since `z ≠ 0` this says `P *ᵥ v = z⁻¹ • v`, so `z⁻¹` is an eigenvalue,
whence `‖z⁻¹‖ = 1` and therefore `‖z‖ = 1`. -/
theorem finite_RH (σ : Equiv.Perm X) {z : ℂ} (hz : z ≠ 0)
    (hdet : (1 - z • transferMatrix σ).det = 0) : ‖z‖ = 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hv
  -- hv : v - z • (transferMatrix σ *ᵥ v) = 0
  have h1 : z • ((transferMatrix σ).mulVec v) = v := by
    rw [sub_eq_zero] at hv; exact hv.symm
  have key : (transferMatrix σ).mulVec v = z⁻¹ • v := by
    calc (transferMatrix σ).mulVec v
        = z⁻¹ • (z • ((transferMatrix σ).mulVec v)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • v := by rw [h1]
  have hn := eigenvalue_norm_eq_one σ ⟨v, hv0, key⟩
  rwa [norm_inv, inv_eq_one] at hn

/-! ## Instantiation for the phase-depth transfer permutation `σ_c`

Restated (self-contained) from `Brockian.PhaseDepthCycles`: the transfer permutation on
the finite state space `S = ZMod 5 × A` is `σ_c(j, a) = (j + 1, a + c j)`. -/

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The phase-depth transfer map `σ_c(j,a) = (j+1, a + c j)` on `S = ZMod 5 × A`. -/
def sigmaMap (c : ZMod 5 → A) (x : ZMod 5 × A) : ZMod 5 × A := (x.1 + 1, x.2 + c x.1)

theorem sigma_injective (c : ZMod 5 → A) : Function.Injective (sigmaMap c) := by
  intro x y h
  simp only [sigmaMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx1 : x.1 = y.1 := add_right_cancel h1
  have hx2 : x.2 = y.2 := by
    rw [hx1] at h2
    exact add_right_cancel h2
  exact Prod.ext hx1 hx2

theorem sigma_bijective (c : ZMod 5 → A) : Function.Bijective (sigmaMap c) :=
  (Finite.injective_iff_bijective).mp (sigma_injective c)

/-- The phase-depth transfer permutation `σ_c` bundled as a permutation of `S`. -/
noncomputable def sigmaPerm (c : ZMod 5 → A) : Equiv.Perm (ZMod 5 × A) :=
  Equiv.ofBijective (sigmaMap c) (sigma_bijective c)

/-- **Target 4a — phase-depth finite RH, eigenvalue form.**
Every eigenvalue of the phase-depth transfer operator `transferMatrix (σ_c)` lies on the
unit circle. -/
theorem phase_depth_eigenvalue_norm_one (c : ZMod 5 → A) {μ : ℂ}
    (h : HasEigenvalue (sigmaPerm c) μ) : ‖μ‖ = 1 :=
  eigenvalue_norm_eq_one (sigmaPerm c) h

/-- **Target 4b — phase-depth finite RH, zeta-zero form (headline instantiation).**
Every zero `z ≠ 0` of the phase-depth finite dynamical zeta
`z ↦ det(1 − z • transferMatrix (σ_c))` lies on the unit circle `|z| = 1`. -/
theorem phase_depth_finite_RH (c : ZMod 5 → A) {z : ℂ} (hz : z ≠ 0)
    (hdet : (1 - z • transferMatrix (sigmaPerm c)).det = 0) : ‖z‖ = 1 :=
  finite_RH (sigmaPerm c) hz hdet

/-- The phase-depth transfer operator itself has finite order `P ^ (orderOf σ_c) = 1`. -/
theorem phase_depth_transferMatrix_finite_order (c : ZMod 5 → A) :
    (transferMatrix (sigmaPerm c)) ^ (orderOf (sigmaPerm c)) = 1 :=
  transferMatrix_pow_orderOf_eq_one (sigmaPerm c)

end Brockian.PhaseDepthFiniteRH
