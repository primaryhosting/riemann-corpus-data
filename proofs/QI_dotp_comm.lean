/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The 7-qubit Steane (CSS) code corrects any single-qubit error.
-/

set_option maxRecDepth 10000

namespace QI

/-! ## Binary vectors and the Hamming parity-check matrix -/

/-- Binary vectors of length `7`: the symplectic ("phase space") coordinates of a Pauli
operator on 7 qubits. -/
abbrev Vec := Fin 7 → ZMod 2

/-- The parity-check matrix of the classical `[7,4,3]` Hamming code: the `j`-th column is the
binary expansion of `j + 1`. -/
def hammingH : Fin 3 → Vec := fun i j => if ((j.val + 1) >>> i.val) % 2 = 1 then 1 else 0

/-- The bilinear form `u ⬝ v = ∑ j, u j * v j` on binary vectors. -/
def dotp (u v : Vec) : ZMod 2 := ∑ j, u j * v j

lemma dotp_comm (u v : Vec) : dotp u v = dotp v u := by
  simp [dotp, mul_comm]

lemma dotp_add_right (u v w : Vec) : dotp u (v + w) = dotp u v + dotp u w := by
  simp [dotp, mul_add, Finset.sum_add_distrib]

lemma dotp_add_left (u v w : Vec) : dotp (u + v) w = dotp u w + dotp v w := by
  simp [dotp, add_mul, Finset.sum_add_distrib]

lemma dotp_zero_right (u : Vec) : dotp u 0 = 0 := by simp [dotp]

lemma dotp_zero_left (u : Vec) : dotp 0 u = 0 := by simp [dotp]

/-! ## Elementary `ZMod 2` facts -/

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

lemma zmod2_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  rcases zmod2_cases x with h | h
  · exact absurd h hx
  · exact h

lemma zmod2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by revert x y; decide

lemma zmod2_solve {x y : ZMod 2} (h : x + y = 1) : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  revert h; revert x y; decide

lemma vec_add_self (a : Vec) : a + a = 0 := by
  funext j
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  simpa using h (a j)

/-! ## Single-qubit Pauli errors -/

/-- The four single-qubit Pauli operators (up to phase). -/
inductive Pauli where
  | I | X | Y | Z
deriving DecidableEq, Fintype, Repr

/-- The `X`-component of a Pauli in the symplectic representation. -/
def Pauli.xbit : Pauli → ZMod 2
  | .X => 1 | .Y => 1 | _ => 0

/-- The `Z`-component of a Pauli in the symplectic representation. -/
def Pauli.zbit : Pauli → ZMod 2
  | .Z => 1 | .Y => 1 | _ => 0

/-- A single-qubit error: a Pauli operator acting on one of the seven qubits. -/
structure SingleQubitError where
  site : Fin 7
  pauli : Pauli
deriving DecidableEq, Fintype, Repr

/-- The `X`-part of a single-qubit error. -/
def SingleQubitError.xvec (E : SingleQubitError) : Vec :=
  fun j => if j = E.site then E.pauli.xbit else 0

/-- The `Z`-part of a single-qubit error. -/
def SingleQubitError.zvec (E : SingleQubitError) : Vec :=
  fun j => if j = E.site then E.pauli.zbit else 0

/-- The error syndrome: the six parity bits obtained by measuring the six Steane stabilizer
generators.  The first triple is measured by the `X`-type generators (detecting `Z` errors),
the second triple by the `Z`-type generators (detecting `X` errors). -/
def syndrome (E : SingleQubitError) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (fun i => dotp (hammingH i) E.zvec, fun i => dotp (hammingH i) E.xvec)

/-- Distinct syndromes for distinct single-qubit error operators: this is exactly the statement
that the classical Hamming code has minimum distance `3`, applied to the `X`- and `Z`-parts
separately. -/
theorem syndrome_injective (E₁ E₂ : SingleQubitError) (h : syndrome E₁ = syndrome E₂) :
    E₁.xvec = E₂.xvec ∧ E₁.zvec = E₂.zvec := by
  revert h; revert E₁ E₂; decide

/-! ### An explicit syndrome decoder -/

/-- All 28 single-qubit errors. -/
def allErrors : List SingleQubitError :=
  (List.finRange 7).flatMap (fun q => [Pauli.I, Pauli.X, Pauli.Y, Pauli.Z].map (fun p => ⟨q, p⟩))

/-- The lookup-table decoder: given a syndrome, return a single-qubit error producing it. -/
def decode (s : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : SingleQubitError :=
  (allErrors.find? (fun E => syndrome E = s)).getD ⟨0, Pauli.I⟩

/-- The decoder recovers the action of any single-qubit error from its syndrome. -/
theorem decode_syndrome (E : SingleQubitError) :
    (decode (syndrome E)).xvec = E.xvec ∧ (decode (syndrome E)).zvec = E.zvec := by
  revert E; decide

/-! ## The 7-qubit Hilbert space and Pauli operators -/

/-- The state space of 7 qubits: complex functions on the `2^7` computational basis states. -/
abbrev QState := Vec → ℂ

/-- The sign character `(-1)^x` of `ZMod 2`. -/
def sgn (x : ZMod 2) : ℂ := if x = 0 then 1 else -1

lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_one : sgn 1 = -1 := by
  rw [sgn, if_neg (by decide : ¬((1 : ZMod 2) = 0))]

lemma sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
  · rw [zero_add, sgn_zero]; ring
  · rw [zero_add, sgn_zero]; ring
  · rw [add_zero, sgn_zero]; ring
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, sgn_zero, sgn_one]; ring

lemma sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  rcases zmod2_cases x with rfl | rfl <;> norm_num [sgn_zero, sgn_one]

lemma sgn_conj (x : ZMod 2) : (starRingEnd ℂ) (sgn x) = sgn x := by
  rcases zmod2_cases x with rfl | rfl <;> simp [sgn_zero, sgn_one]

/-- The Pauli operator `X^a Z^b` acting on the 7-qubit state space (global phases are
irrelevant to error correction, so we fix this convention). -/
def Pop (a b : Vec) (psi : QState) : QState := fun v => sgn (dotp b (v + a)) * psi (v + a)

/-- The Hermitian inner product on the 7-qubit state space. -/
noncomputable def qinner (psi phi : QState) : ℂ := ∑ v, (starRingEnd ℂ) (psi v) * phi v

lemma qinner_smul_right (c : ℂ) (psi phi : QState) :
    qinner psi (fun v => c * phi v) = c * qinner psi phi := by
  simp only [qinner, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun v _ => by ring)

lemma Pop_zero (psi : QState) : Pop 0 0 psi = psi := by
  funext v; simp [Pop, dotp_zero_left, sgn_zero]

/-- Composition of Pauli operators, up to the expected sign. -/
lemma Pop_comp (a b a' b' : Vec) (psi : QState) :
    Pop a b (Pop a' b' psi) = fun v => sgn (dotp b a') * Pop (a + a') (b + b') psi v := by
  funext v
  have hassoc : v + a + a' = v + (a + a') := add_assoc _ _ _
  have d1 : dotp b (v + a) = dotp b v + dotp b a := dotp_add_right _ _ _
  have d2 : dotp b' (v + (a + a')) = dotp b' v + (dotp b' a + dotp b' a') := by
    rw [dotp_add_right, dotp_add_right]
  have d3 : dotp (b + b') (v + (a + a'))
      = (dotp b v + (dotp b a + dotp b a')) + (dotp b' v + (dotp b' a + dotp b' a')) := by
    rw [dotp_add_left, dotp_add_right, dotp_add_right, dotp_add_right, dotp_add_right]
  simp only [Pop, hassoc, d1, d2, d3, sgn_add]
  linear_combination (-(sgn (dotp b v) * sgn (dotp b a) * sgn (dotp b' v) * sgn (dotp b' a) *
    sgn (dotp b' a') * psi (v + (a + a')))) * sgn_mul_self (dotp b a')

/-- Moving a Pauli operator across the inner product. -/
lemma qinner_Pop_left (a b : Vec) (psi phi : QState) :
    qinner (Pop a b psi) phi = sgn (dotp b a) * qinner psi (Pop a b phi) := by
  have hsum : ∑ v : Vec, (starRingEnd ℂ) (Pop a b psi v) * phi v
      = ∑ w : Vec, (starRingEnd ℂ) (Pop a b psi (w + a)) * phi (w + a) :=
    (Fintype.sum_equiv (Equiv.addRight a)
      (fun w => (starRingEnd ℂ) (Pop a b psi (w + a)) * phi (w + a))
      (fun v => (starRingEnd ℂ) (Pop a b psi v) * phi v) (fun _ => rfl)).symm
  simp only [qinner, hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hw : w + a + a = w := by rw [add_assoc, vec_add_self, add_zero]
  simp only [Pop, hw]
  rw [dotp_add_right b w a]
  simp only [sgn_add, map_mul, sgn_conj]
  linear_combination (-(sgn (dotp b w) * (starRingEnd ℂ) (psi w) * phi (w + a))) *
    sgn_mul_self (dotp b a)

/-! ## The Steane code space -/

/-- The Steane code space: the joint `+1` eigenspace of the six stabilizer generators, three
`X`-type and three `Z`-type, both families given by the rows of the Hamming parity-check
matrix. -/
def CodeSpace : Set QState :=
  {psi | ∀ i : Fin 3, Pop (hammingH i) 0 psi = psi ∧ Pop 0 (hammingH i) psi = psi}

/-- Membership in the simplex code `C⊥`, the row space of the Hamming parity-check matrix. -/
def inSimplex (v : Vec) : Prop := ∃ c : Fin 3 → ZMod 2, ∀ j, v j = ∑ i, c i * hammingH i j

instance : DecidablePred inSimplex := fun v => by unfold inSimplex; infer_instance

/-- The all-ones vector, a Hamming codeword outside the simplex code. -/
def ones : Vec := fun _ => 1

lemma simplex_shift (i : Fin 3) (v : Vec) : inSimplex (v + hammingH i) ↔ inSimplex v := by
  revert i v; decide

lemma simplex_orthogonal (i : Fin 3) (v : Vec) (hv : inSimplex v) : dotp (hammingH i) v = 0 := by
  revert hv; revert i v; decide

lemma simplex_zero : inSimplex 0 := by decide

lemma simplex_disjoint (v : Vec) : ¬ (inSimplex v ∧ inSimplex (v + ones)) := by
  revert v; decide

lemma dotp_hammingH_ones (i : Fin 3) : dotp (hammingH i) ones = 0 := by
  revert i; decide

/-- The logical `|0⟩` state: the uniform superposition over the simplex code `C⊥`. -/
def logical0 : QState := fun v => if inSimplex v then 1 else 0

/-- The logical `|1⟩` state: the uniform superposition over the coset `𝟙 + C⊥`. -/
def logical1 : QState := fun v => if inSimplex (v + ones) then 1 else 0

lemma logical0_mem : logical0 ∈ CodeSpace := by
  intro i
  constructor
  · funext v
    simp only [Pop, logical0, dotp_zero_left, sgn_zero, one_mul]
    by_cases h : inSimplex (v + hammingH i)
    · rw [if_pos h, if_pos ((simplex_shift i v).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((simplex_shift i v).mpr hc))]
  · funext v
    simp only [Pop, logical0, add_zero]
    by_cases h : inSimplex v
    · rw [if_pos h, simplex_orthogonal i v h, sgn_zero, one_mul]
    · rw [if_neg h, mul_zero]

lemma logical1_mem : logical1 ∈ CodeSpace := by
  intro i
  constructor
  · funext v
    simp only [Pop, logical1, dotp_zero_left, sgn_zero, one_mul]
    have hrw : v + hammingH i + ones = (v + ones) + hammingH i := by
      rw [add_assoc, add_comm (hammingH i) ones, ← add_assoc]
    rw [hrw]
    by_cases h : inSimplex ((v + ones) + hammingH i)
    · rw [if_pos h, if_pos ((simplex_shift i (v + ones)).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((simplex_shift i (v + ones)).mpr hc))]
  · funext v
    simp only [Pop, logical1, add_zero]
    by_cases h : inSimplex (v + ones)
    · have h0 : dotp (hammingH i) (v + ones) = 0 := simplex_orthogonal i _ h
      rw [dotp_add_right, dotp_hammingH_ones, add_zero] at h0
      rw [if_pos h, h0, sgn_zero, one_mul]
    · rw [if_neg h, mul_zero]

lemma logical0_ne_zero : logical0 ≠ 0 := by
  intro h
  have h2 : logical0 0 = (0 : QState) 0 := by rw [h]
  simp only [logical0, if_pos simplex_zero, Pi.zero_apply] at h2
  exact one_ne_zero h2

lemma logical1_ne_zero : logical1 ≠ 0 := by
  intro h
  have h2 : logical1 ones = (0 : QState) ones := by rw [h]
  simp only [logical1, Pi.zero_apply] at h2
  rw [vec_add_self, if_pos simplex_zero] at h2
  exact one_ne_zero h2

lemma logical_orthogonal : qinner logical0 logical1 = 0 := by
  refine Finset.sum_eq_zero (fun v _ => ?_)
  by_cases h : inSimplex v
  · have h2 : ¬ inSimplex (v + ones) := fun hc => simplex_disjoint v ⟨h, hc⟩
    simp [logical1, h2]
  · simp [logical0, h]

/-! ## Knill–Laflamme error-correction conditions -/

/-- The unitary implementing a single-qubit Pauli error. -/
def errOp (E : SingleQubitError) : QState → QState := Pop E.xvec E.zvec

/-- Key lemma: if a stabilizer generator anticommutes with the Pauli operator `(A, B)`, then
that operator has vanishing matrix elements between code states. -/
lemma qinner_eq_zero_of_anticomm {A B ga gb : Vec} {psi phi : QState}
    (hg : dotp ga gb = 0) (hpsi : Pop ga gb psi = psi) (hphi : Pop ga gb phi = phi)
    (hanti : dotp ga B + dotp gb A = 1) :
    qinner psi (Pop A B phi) = 0 := by
  set X := qinner psi (Pop (A + ga) (B + gb) phi) with hX
  have r1 : qinner psi (Pop A B phi) = sgn (dotp B ga) * X := by
    conv_lhs => rw [← hphi]
    rw [Pop_comp A B ga gb phi, qinner_smul_right, hX]
  have r2 : qinner psi (Pop A B phi) = sgn (dotp gb A) * X := by
    conv_lhs => rw [← hpsi]
    rw [qinner_Pop_left ga gb psi (Pop A B phi), dotp_comm gb ga, hg, sgn_zero, one_mul,
      Pop_comp ga gb A B phi, qinner_smul_right, hX, add_comm ga A, add_comm gb B]
  have hsign : sgn (dotp B ga) = - sgn (dotp gb A) := by
    rw [dotp_comm B ga]
    rcases zmod2_solve hanti with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [h1, h2, sgn_zero, sgn_one]
  have hneg : qinner psi (Pop A B phi) = - qinner psi (Pop A B phi) := by
    conv_lhs => rw [r1]
    rw [hsign, r2]; ring
  linear_combination hneg / 2

/-- The Knill–Laflamme condition for the Steane code and the set of all single-qubit Pauli
errors: for any two single-qubit errors `E₁`, `E₂` there is a constant `c` (independent of the
code states) such that `⟨E₁ ψ, E₂ φ⟩ = c ⟨ψ, φ⟩` for all code states `ψ`, `φ`.  By the
Knill–Laflamme theorem this is precisely the statement that every single-qubit error is
correctable. -/
theorem knill_laflamme (E₁ E₂ : SingleQubitError) :
    ∃ c : ℂ, ∀ psi phi : QState, psi ∈ CodeSpace → phi ∈ CodeSpace →
      qinner (errOp E₁ psi) (errOp E₂ phi) = c * qinner psi phi := by
  refine ⟨if syndrome E₁ = syndrome E₂ then
    sgn (dotp E₁.zvec E₁.xvec) * sgn (dotp E₁.zvec E₂.xvec) else 0, ?_⟩
  intro psi phi hpsi hphi
  have key : qinner (errOp E₁ psi) (errOp E₂ phi)
      = sgn (dotp E₁.zvec E₁.xvec) * sgn (dotp E₁.zvec E₂.xvec) *
        qinner psi (Pop (E₁.xvec + E₂.xvec) (E₁.zvec + E₂.zvec) phi) := by
    show qinner (Pop E₁.xvec E₁.zvec psi) (Pop E₂.xvec E₂.zvec phi) = _
    rw [qinner_Pop_left E₁.xvec E₁.zvec psi (Pop E₂.xvec E₂.zvec phi),
      Pop_comp E₁.xvec E₁.zvec E₂.xvec E₂.zvec phi, qinner_smul_right]
    ring
  by_cases hs : syndrome E₁ = syndrome E₂
  · obtain ⟨hx, hz⟩ := syndrome_injective E₁ E₂ hs
    have ha : E₁.xvec + E₂.xvec = 0 := by rw [hx]; exact vec_add_self _
    have hb : E₁.zvec + E₂.zvec = 0 := by rw [hz]; exact vec_add_self _
    rw [key, ha, hb, Pop_zero, if_pos hs]
  · rw [key, if_neg hs, zero_mul]
    have hne : (fun i => dotp (hammingH i) E₁.zvec) ≠ (fun i => dotp (hammingH i) E₂.zvec)
        ∨ (fun i => dotp (hammingH i) E₁.xvec) ≠ (fun i => dotp (hammingH i) E₂.xvec) := by
      by_contra hc
      push_neg at hc
      exact hs (by unfold syndrome; rw [hc.1, hc.2])
    have hzero : qinner psi (Pop (E₁.xvec + E₂.xvec) (E₁.zvec + E₂.zvec) phi) = 0 := by
      rcases hne with hne | hne
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
        have hB : dotp (hammingH i) (E₁.zvec + E₂.zvec) = 1 := by
          rw [dotp_add_right]
          exact zmod2_ne_zero (fun hc => hi ((zmod2_add_eq_zero_iff _ _).mp hc))
        exact qinner_eq_zero_of_anticomm (ga := hammingH i) (gb := 0)
          (dotp_zero_right _) (hpsi i).1 (hphi i).1
          (by rw [hB, dotp_zero_left, add_zero])
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
        have hA : dotp (hammingH i) (E₁.xvec + E₂.xvec) = 1 := by
          rw [dotp_add_right]
          exact zmod2_ne_zero (fun hc => hi ((zmod2_add_eq_zero_iff _ _).mp hc))
        exact qinner_eq_zero_of_anticomm (ga := 0) (gb := hammingH i)
          (dotp_zero_left _) (hpsi i).2 (hphi i).2
          (by rw [hA, dotp_zero_left, zero_add])
    rw [hzero, mul_zero]

/-- **The 7-qubit Steane code corrects any single-qubit error.**

Part 1: the code space is a genuine quantum code — it contains two orthogonal nonzero states
(the logical `|0⟩` and `|1⟩`), so it encodes at least one logical qubit.

Part 2: the Knill–Laflamme error-correction conditions hold for the set of *all* single-qubit
Pauli errors (`I`, `X`, `Y`, `Z` on any of the seven qubits); hence there exists a recovery
operation correcting every single-qubit error.

Part 3 (constructive): the syndrome of a single-qubit error determines its action, and the
explicit lookup decoder `decode` recovers it. -/
theorem steane_code :
    (logical0 ∈ CodeSpace ∧ logical1 ∈ CodeSpace ∧ logical0 ≠ 0 ∧ logical1 ≠ 0 ∧
        qinner logical0 logical1 = 0) ∧
    (∀ E₁ E₂ : SingleQubitError, ∃ c : ℂ, ∀ psi phi : QState,
        psi ∈ CodeSpace → phi ∈ CodeSpace →
        qinner (errOp E₁ psi) (errOp E₂ phi) = c * qinner psi phi) ∧
    (∀ E : SingleQubitError,
        (decode (syndrome E)).xvec = E.xvec ∧ (decode (syndrome E)).zvec = E.zvec) :=
  ⟨⟨logical0_mem, logical1_mem, logical0_ne_zero, logical1_ne_zero, logical_orthogonal⟩,
    knill_laflamme, decode_syndrome⟩

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

