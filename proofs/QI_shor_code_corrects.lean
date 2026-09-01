/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header comment above uses `/- ... -/` rather than `/-! ... -/`: Lean requires all
-- `import` lines to precede any module docstring, so a `/-!` block cannot open the file.)

import Mathlib

open scoped BigOperators

/-!
# The 9-qubit Shor code corrects an arbitrary single-qubit error

The 9 qubits are grouped into three blocks of three, so a computational basis state of the
register is an element of `Cfg = Blk × Blk × Blk` with `Blk = Bool × Bool × Bool`, and a state
vector is a function `Cfg → ℂ` of amplitudes.

The logical codewords are

* `|0_L⟩ = (|000⟩ + |111⟩)^{⊗3} / (2√2)`,
* `|1_L⟩ = (|000⟩ - |111⟩)^{⊗3} / (2√2)`.

An arbitrary single-qubit error acting on qubit `j` of block `k` is given by an arbitrary
`2 × 2` complex matrix `A : Bool → Bool → ℂ` (no linearity, unitarity or normalization is
assumed).  The main theorem `QI.shor_code_corrects` establishes the Knill–Laflamme
error-correction conditions
`⟨c_a | A† B | c_b⟩ = δ_{a b} · α(A, B)`
for all pairs of single-qubit operators `A`, `B` placed at arbitrary (possibly different) qubits.
Note that `⟨c_a | A† B | c_b⟩ = ⟨A c_a , B c_b⟩`, which is the form used below.  Since every
single-qubit error operator is one of these and error channels are linear, these conditions are
exactly the statement that the code corrects an arbitrary single-qubit error.
-/

namespace QI

/-- Computational basis states of one 3-qubit block. -/
abbrev Blk := Bool × Bool × Bool

/-- Computational basis states of the 9-qubit register, grouped into three blocks. -/
abbrev Cfg := Blk × Blk × Blk

/-- Read qubit `j` of a block. -/
def getQ (v : Blk) : Fin 3 → Bool
  | 0 => v.1
  | 1 => v.2.1
  | 2 => v.2.2

/-- Overwrite qubit `j` of a block. -/
def setQ (v : Blk) : Fin 3 → Bool → Blk
  | 0, p => (p, v.2.1, v.2.2)
  | 1, p => (v.1, p, v.2.2)
  | 2, p => (v.1, v.2.1, p)

/-- Read block `k` of the register. -/
def getB (w : Cfg) : Fin 3 → Blk
  | 0 => w.1
  | 1 => w.2.1
  | 2 => w.2.2

/-- Overwrite block `k` of the register. -/
def setB (w : Cfg) : Fin 3 → Blk → Cfg
  | 0, u => (u, w.2.1, w.2.2)
  | 1, u => (w.1, u, w.2.2)
  | 2, u => (w.1, w.2.1, u)

/-- Amplitudes of the unnormalized block states `|000⟩ + |111⟩` (for `a = false`) and
`|000⟩ - |111⟩` (for `a = true`). -/
noncomputable def blk (a : Bool) : Blk → ℂ := fun v =>
  if v = (false, false, false) then 1
  else if v = (true, true, true) then (if a then -1 else 1) else 0

/-- The product state over the three blocks with block amplitudes `g₁`, `g₂`, `g₃`. -/
noncomputable def tri (g₁ g₂ g₃ : Blk → ℂ) : Cfg → ℂ :=
  fun w => g₁ w.1 * g₂ w.2.1 * g₃ w.2.2

/-- The normalization constant of the Shor codewords. -/
noncomputable def nrm : ℂ := ((1 / (2 * Real.sqrt 2) : ℝ) : ℂ)

/-- The two logical codewords of the 9-qubit Shor code:
`|0_L⟩ = (|000⟩+|111⟩)^{⊗3}/(2√2)` and `|1_L⟩ = (|000⟩-|111⟩)^{⊗3}/(2√2)`. -/
noncomputable def cw (a : Bool) : Cfg → ℂ := fun w => nrm * tri (blk a) (blk a) (blk a) w

/-- The Hermitian inner product on the 9-qubit state space. -/
noncomputable def ip (f g : Cfg → ℂ) : ℂ := ∑ w : Cfg, (starRingEnd ℂ) (f w) * g w

/-- The Hermitian inner product on the state space of a single block. -/
noncomputable def ipB (g h : Blk → ℂ) : ℂ := ∑ v : Blk, (starRingEnd ℂ) (g v) * h v

/-- The single-qubit operator `A` applied at qubit `j` of a block. -/
noncomputable def actQ (A : Bool → Bool → ℂ) (j : Fin 3) (g : Blk → ℂ) : Blk → ℂ :=
  fun v => ∑ p : Bool, A (getQ v j) p * g (setQ v j p)

/-- The single-qubit operator `A` applied at qubit `j` of block `k` of the 9-qubit register. -/
noncomputable def act (A : Bool → Bool → ℂ) (k j : Fin 3) (f : Cfg → ℂ) : Cfg → ℂ :=
  fun w => ∑ p : Bool, A (getQ (getB w k) j) p * f (setB w k (setQ (getB w k) j p))

/-! ### Basic algebraic lemmas -/

lemma act_const_mul (A : Bool → Bool → ℂ) (k j : Fin 3) (c : ℂ) (f : Cfg → ℂ) :
    act A k j (fun w => c * f w) = fun w => c * act A k j f w := by
  funext w
  simp only [act, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

lemma ip_const_mul (c d : ℂ) (f g : Cfg → ℂ) :
    ip (fun w => c * f w) (fun w => d * g w) = (starRingEnd ℂ) c * d * ip f g := by
  simp only [ip, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The inner product of two product states factors over the three blocks. -/
lemma ip_tri (g₁ g₂ g₃ h₁ h₂ h₃ : Blk → ℂ) :
    ip (tri g₁ g₂ g₃) (tri h₁ h₂ h₃) = ipB g₁ h₁ * ipB g₂ h₂ * ipB g₃ h₃ := by
  have hip : ip (tri g₁ g₂ g₃) (tri h₁ h₂ h₃)
      = ∑ v₁ : Blk, ∑ v₂ : Blk, ∑ v₃ : Blk,
        ((starRingEnd ℂ) (g₁ v₁) * h₁ v₁) *
          (((starRingEnd ℂ) (g₂ v₂) * h₂ v₂) * ((starRingEnd ℂ) (g₃ v₃) * h₃ v₃)) := by
    rw [ip, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v₁ _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v₂ _ => Finset.sum_congr rfl fun v₃ _ => ?_
    simp only [tri, map_mul]; ring
  rw [hip, ipB, ipB, ipB, mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun v₁ _ => Finset.sum_congr rfl fun v₂ _ => ?_
  rw [Finset.mul_sum]

lemma act_tri_zero (A : Bool → Bool → ℂ) (j : Fin 3) (g₁ g₂ g₃ : Blk → ℂ) :
    act A 0 j (tri g₁ g₂ g₃) = tri (actQ A j g₁) g₂ g₃ := by
  funext w
  simp only [act, tri, actQ, getB, setB, Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

lemma act_tri_one (A : Bool → Bool → ℂ) (j : Fin 3) (g₁ g₂ g₃ : Blk → ℂ) :
    act A 1 j (tri g₁ g₂ g₃) = tri g₁ (actQ A j g₂) g₃ := by
  funext w
  simp only [act, tri, actQ, getB, setB, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

lemma act_tri_two (A : Bool → Bool → ℂ) (j : Fin 3) (g₁ g₂ g₃ : Blk → ℂ) :
    act A 2 j (tri g₁ g₂ g₃) = tri g₁ g₂ (actQ A j g₃) := by
  funext w
  simp only [act, tri, actQ, getB, setB, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-! ### Block-level computations -/

/-- The two block states are orthogonal and both have squared norm `2`. -/
lemma ipB_blk (a b : Bool) : ipB (blk a) (blk b) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> simp [ipB, blk, Fintype.sum_prod_type] <;> norm_num

/-- A single-qubit operator acting on the left block state gives the same overlap with
either logical value: the identity part contributes and the `Z` part is killed by
orthogonality. -/
lemma ipB_actQ_left (A : Bool → Bool → ℂ) (j : Fin 3) :
    ipB (actQ A j (blk true)) (blk true) = ipB (actQ A j (blk false)) (blk false) := by
  fin_cases j <;> simp [ipB, blk, actQ, getQ, setQ, Fintype.sum_prod_type]

lemma ipB_actQ_right (B : Bool → Bool → ℂ) (j : Fin 3) :
    ipB (blk true) (actQ B j (blk true)) = ipB (blk false) (actQ B j (blk false)) := by
  fin_cases j <;> simp [ipB, blk, actQ, getQ, setQ, Fintype.sum_prod_type]

set_option maxHeartbeats 1000000 in
/-- Two single-qubit operators inside the same block give the same overlap for either
logical value. -/
lemma ipB_actQ_both (A B : Bool → Bool → ℂ) (j₁ j₂ : Fin 3) :
    ipB (actQ A j₁ (blk true)) (actQ B j₂ (blk true))
      = ipB (actQ A j₁ (blk false)) (actQ B j₂ (blk false)) := by
  fin_cases j₁ <;> fin_cases j₂ <;> simp [ipB, blk, actQ, getQ, setQ, Fintype.sum_prod_type]

/-! ### The Knill–Laflamme conditions -/

private lemma fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

/-- Knill–Laflamme conditions for the unnormalized codewords. -/
lemma ip_act_tri_blk (A B : Bool → Bool → ℂ) (k₁ j₁ k₂ j₂ : Fin 3) (a b : Bool) :
    ip (act A k₁ j₁ (tri (blk a) (blk a) (blk a))) (act B k₂ j₂ (tri (blk b) (blk b) (blk b)))
      = if a = b then ip (act A k₁ j₁ (tri (blk false) (blk false) (blk false)))
                        (act B k₂ j₂ (tri (blk false) (blk false) (blk false))) else 0 := by
  rcases fin3_cases k₁ with h₁ | h₁ | h₁ <;> rcases fin3_cases k₂ with h₂ | h₂ | h₂ <;>
    subst h₁ <;> subst h₂ <;>
    simp only [act_tri_zero, act_tri_one, act_tri_two, ip_tri] <;>
    cases a <;> cases b <;>
    simp [ipB_blk, ipB_actQ_left, ipB_actQ_right, ipB_actQ_both]

lemma nrm_mul_self : (starRingEnd ℂ) nrm * nrm = 1 / 8 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have : (1 / (2 * Real.sqrt 2) : ℝ) * (1 / (2 * Real.sqrt 2) : ℝ) = 1 / 8 := by
    field_simp
    nlinarith [h2, Real.sqrt_nonneg 2]
  rw [nrm, Complex.conj_ofReal, ← Complex.ofReal_mul, this]
  norm_num

/-! ### The codewords are orthonormal -/

theorem shor_codewords_orthonormal (a b : Bool) :
    ip (cw a) (cw b) = if a = b then 1 else 0 := by
  have h : ip (cw a) (cw b)
      = (starRingEnd ℂ) nrm * nrm * ip (tri (blk a) (blk a) (blk a))
          (tri (blk b) (blk b) (blk b)) := by
    rw [show cw a = fun w => nrm * tri (blk a) (blk a) (blk a) w from rfl,
        show cw b = fun w => nrm * tri (blk b) (blk b) (blk b) w from rfl, ip_const_mul]
  rw [h, nrm_mul_self, ip_tri, ipB_blk]
  cases a <;> cases b <;> norm_num

/-- **The 9-qubit Shor code corrects an arbitrary single-qubit error.**
For arbitrary single-qubit operators `A`, `B` acting on arbitrary (possibly different) qubits
`(k₁, j₁)` and `(k₂, j₂)` of the register, the Knill–Laflamme error-correction conditions hold
for the two logical codewords: `⟨A c_a, B c_b⟩ = ⟨c_a | A† B | c_b⟩ = δ_{ab} · α` with the
constant `α` independent of the logical state `a`.  Since an arbitrary single-qubit error is a
linear combination of such operators, this is exactly the statement that the code corrects an
arbitrary single-qubit error (equivalently, a recovery channel exists). -/
theorem shor_code_corrects (k₁ j₁ k₂ j₂ : Fin 3) (A B : Bool → Bool → ℂ) :
    ∃ α : ℂ, ∀ a b : Bool,
      ip (act A k₁ j₁ (cw a)) (act B k₂ j₂ (cw b)) = if a = b then α else 0 := by
  have hred : ∀ a b : Bool, ip (act A k₁ j₁ (cw a)) (act B k₂ j₂ (cw b))
      = (starRingEnd ℂ) nrm * nrm *
          ip (act A k₁ j₁ (tri (blk a) (blk a) (blk a)))
            (act B k₂ j₂ (tri (blk b) (blk b) (blk b))) := by
    intro a b
    rw [show cw a = fun w => nrm * tri (blk a) (blk a) (blk a) w from rfl,
        show cw b = fun w => nrm * tri (blk b) (blk b) (blk b) w from rfl,
        act_const_mul, act_const_mul, ip_const_mul]
  refine ⟨ip (act A k₁ j₁ (cw false)) (act B k₂ j₂ (cw false)), fun a b => ?_⟩
  rw [hred, hred, ip_act_tri_blk]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]

/-! ### A sanity check: the identity error -/

lemma setQ_getQ (v : Blk) (j : Fin 3) : setQ v j (getQ v j) = v := by
  fin_cases j <;> simp [setQ, getQ]

lemma setB_getB (w : Cfg) (k : Fin 3) : setB w k (getB w k) = w := by
  fin_cases k <;> simp [setB, getB]

/-- Applying the identity operator at any qubit does nothing. -/
lemma act_id (k j : Fin 3) (f : Cfg → ℂ) :
    act (fun p q => if p = q then 1 else 0) k j f = f := by
  funext w
  simp only [act, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [setQ_getQ, setB_getB]

/-- Non-vacuity check: for the identity error the Knill-Laflamme constant is `1`, so the
statement of `shor_code_corrects` is not vacuous. -/
theorem shor_code_identity_error (k j : Fin 3) (a : Bool) :
    ip (act (fun p q => if p = q then 1 else 0) k j (cw a))
      (act (fun p q => if p = q then 1 else 0) k j (cw a)) = 1 := by
  rw [act_id, shor_codewords_orthonormal]
  simp

end QI

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

