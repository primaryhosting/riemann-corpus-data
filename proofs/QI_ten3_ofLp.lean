import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Statement: There is no unitary that deletes an unknown quantum state (no-deleting theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- A qubit: the two dimensional complex Hilbert space. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The ancilla register: an `m`-dimensional complex Hilbert space. -/
abbrev Anc (m : ℕ) : Type := EuclideanSpace ℂ (Fin m)

/-- The full register: two qubits together with an `m`-dimensional ancilla,
realized concretely as the Hilbert space with index set `Fin 2 × Fin 2 × Fin m`. -/
abbrev Reg (m : ℕ) : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin m)

/-- The (unnormalized) product state `a ⊗ b ⊗ c` inside `Reg m`. -/
def ten3 {m : ℕ} (a b : Qubit) (c : Anc m) : Reg m :=
  WithLp.toLp 2 (fun p => a.ofLp p.1 * b.ofLp p.2.1 * c.ofLp p.2.2)

@[simp]
lemma ten3_ofLp {m : ℕ} (a b : Qubit) (c : Anc m) (p : Fin 2 × Fin 2 × Fin m) :
    (ten3 a b c).ofLp p = a.ofLp p.1 * b.ofLp p.2.1 * c.ofLp p.2.2 := rfl

/-- Inner products of product states factor as the product of the inner products. -/
lemma inner_ten3 {m : ℕ} (a b : Qubit) (c : Anc m) (a' b' : Qubit) (c' : Anc m) :
    ⟪ten3 a b c, ten3 a' b' c'⟫_ℂ = ⟪a, a'⟫_ℂ * ⟪b, b'⟫_ℂ * ⟪c, c'⟫_ℂ := by
  have hprod : ∀ f : Fin 2 → ℂ, ∀ g : Fin 2 → ℂ, ∀ h : Fin m → ℂ,
      ∑ p : Fin 2 × Fin 2 × Fin m, f p.1 * g p.2.1 * h p.2.2
        = (∑ i, f i) * (∑ j, g j) * (∑ k, h k) := by
    intro f g h
    simp_rw [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [PiLp.inner_apply, RCLike.inner_apply, ten3_ofLp, map_mul]
  have := hprod (fun i => a'.ofLp i * (starRingEnd ℂ) (a.ofLp i))
    (fun j => b'.ofLp j * (starRingEnd ℂ) (b.ofLp j))
    (fun k => c'.ofLp k * (starRingEnd ℂ) (c.ofLp k))
  rw [← this]
  exact Finset.sum_congr rfl (fun p _ => by ring)

/-- The scalar `1/√2`, viewed as a complex number. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The state `|0⟩`. -/
noncomputable def psi0 : Qubit := WithLp.toLp 2 ![1, 0]

/-- The state `(|0⟩ + |1⟩)/√2`. -/
noncomputable def psiPlus : Qubit := WithLp.toLp 2 ![invSqrtTwo, invSqrtTwo]

lemma invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrtTwo, ← mul_inv, h]
  norm_num

lemma norm_psi0 : ‖psi0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [psi0, Fin.sum_univ_two]

lemma norm_psiPlus : ‖psiPlus‖ = 1 := by
  have h2 : ‖invSqrtTwo‖ ^ 2 = 1 / 2 := by
    have : ‖invSqrtTwo‖ ^ 2 = ‖invSqrtTwo * invSqrtTwo‖ := by
      rw [norm_mul]; ring
    rw [this, invSqrtTwo_sq]
    norm_num
  rw [EuclideanSpace.norm_eq]
  simp only [psiPlus, WithLp.ofLp_toLp, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, h2]
  norm_num

lemma inner_psi0_psiPlus : ⟪psi0, psiPlus⟫_ℂ = invSqrtTwo := by
  simp [PiLp.inner_apply, RCLike.inner_apply, psi0, psiPlus, Fin.sum_univ_two]

/-- **No-deleting theorem.** There is no unitary (linear isometric equivalence) of the
two-qubit-plus-ancilla register which, for every unknown pure qubit state `ψ`, maps the two
copies `ψ ⊗ ψ` together with a fixed ancilla state to `ψ` tensored with a fixed blank state and a
fixed final ancilla state.  In other words, a copy of an unknown quantum state cannot be deleted:
the second copy cannot be replaced by a standard blank state while leaving the ancilla in a state
independent of `ψ`. -/
theorem no_deleting {m : ℕ} (blank : Qubit) (anc ancOut : Anc m)
    (hblank : ‖blank‖ = 1) (hanc : ‖anc‖ = 1) (hancOut : ‖ancOut‖ = 1) :
    ¬ ∃ U : Reg m ≃ₗᵢ[ℂ] Reg m,
      ∀ ψ : Qubit, ‖ψ‖ = 1 → U (ten3 ψ ψ anc) = ten3 ψ blank ancOut := by
  rintro ⟨U, hU⟩
  have key : ⟪ten3 psi0 blank ancOut, ten3 psiPlus blank ancOut⟫_ℂ
      = ⟪ten3 psi0 psi0 anc, ten3 psiPlus psiPlus anc⟫_ℂ := by
    rw [← hU psi0 norm_psi0, ← hU psiPlus norm_psiPlus, U.inner_map_map]
  have hb : ⟪blank, blank⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hblank]; norm_num
  have ha : ⟪anc, anc⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hanc]; norm_num
  have hao : ⟪ancOut, ancOut⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hancOut]; norm_num
  rw [inner_ten3, inner_ten3] at key
  simp only [hb, ha, hao, mul_one, inner_psi0_psiPlus] at key
  -- `key` now reads `invSqrtTwo = invSqrtTwo * invSqrtTwo`
  rw [invSqrtTwo_sq] at key
  have hsq := invSqrtTwo_sq
  rw [key] at hsq
  norm_num at hsq

end QI

