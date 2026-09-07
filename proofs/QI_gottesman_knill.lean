/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/
noncomputable def ph (s : ZMod 4) : ℂ := Complex.I ^ s.val

/-- The sign `(-1) ^ t` attached to `t : ZMod 2`. -/
def psign (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

/-- The (non-additive) inclusion `ZMod 2 → ZMod 4` sending `0 ↦ 0`, `1 ↦ 1`. -/
def lift2 (t : ZMod 2) : ZMod 4 := (t.val : ZMod 4)

lemma zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

@[simp] lemma zmod2_one_add_one : (1 + 1 : ZMod 2) = 0 := by decide

@[simp] lemma lift2_zero : lift2 0 = 0 := by decide

@[simp] lemma lift2_one : lift2 1 = 1 := by decide

@[simp] lemma ph_zero : ph 0 = 1 := by simp [ph]

@[simp] lemma ph_one : ph 1 = Complex.I := by
  rw [ph, show ZMod.val (1 : ZMod 4) = 1 from by decide, pow_one]

@[simp] lemma psign_zero : psign 0 = 1 := by simp [psign]

lemma sum_zmod2 (f : ZMod 2 → ℂ) : ∑ t : ZMod 2, f t = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_pair (by decide)]

lemma I_pow_mod (a : ℕ) : Complex.I ^ a = Complex.I ^ (a % 4) := by
  conv_lhs => rw [← Nat.div_add_mod a 4]
  rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

lemma ph_add (s t : ZMod 4) : ph (s + t) = ph s * ph t := by
  simp only [ph, ZMod.val_add, ← pow_add]
  rw [← I_pow_mod]

lemma ph_two_lift (t : ZMod 2) : ph (2 * lift2 t) = psign t := by
  rcases zmod2_cases t with rfl | rfl
  · simp
  · rw [show (2 * lift2 (1 : ZMod 2) : ZMod 4) = 2 from by decide]
    simp [ph, psign, show ZMod.val (2 : ZMod 4) = 2 from by decide, pow_two, Complex.I_mul_I]

lemma psign_add (s t : ZMod 2) : psign (s + t) = psign s * psign t := by
  rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl <;> simp [psign]

lemma psign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    psign (∑ i ∈ s, f i) = ∏ i ∈ s, psign (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, psign_add, ih]

lemma conj_psign (t : ZMod 2) : (starRingEnd ℂ) (psign t) = psign t := by
  rcases zmod2_cases t with rfl | rfl <;> simp [psign]

/-- `1/√2` as a complex number. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [invSqrt2, ← Complex.ofReal_inv, ← Complex.ofReal_mul, h]
  norm_num

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-! ## Single qubit matrices -/

/-- The single qubit Pauli operator `X ^ x * Z ^ z` (a `2 × 2` matrix). -/
def xz (x z : ZMod 2) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun a b => if a = b + x then psign (z * b) else 0

/-- The Hadamard gate. -/
noncomputable def hmat : Matrix (ZMod 2) (ZMod 2) ℂ := fun a b => invSqrt2 * psign (a * b)

/-- The phase gate `S = diag (1, i)`. -/
noncomputable def smat : Matrix (ZMod 2) (ZMod 2) ℂ :=
  fun a b => if a = b then ph (lift2 a) else 0

lemma hmat_unitary : hmat * hmatᴴ = 1 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hmat, sum_zmod2, Matrix.one_apply]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    simp [psign, conj_invSqrt2, invSqrt2_mul_self] <;> ring

lemma smat_unitary : smat * smatᴴ = 1 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, smat, sum_zmod2, Matrix.one_apply]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    simp [Complex.ext_iff]

/-- `H (X^x Z^z) = (-1)^(x z) (X^z Z^x) H`. -/
lemma hmat_xz (x z : ZMod 2) : hmat * xz x z = psign (x * z) • (xz z x * hmat) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.smul_apply, hmat, xz, smul_eq_mul, sum_zmod2]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases z with rfl | rfl <;>
    simp [psign]

/-- `S (X^x Z^z) = i^x (X^x Z^(x+z)) S`. -/
lemma smat_xz (x z : ZMod 2) : smat * xz x z = ph (lift2 x) • (xz x (x + z) * smat) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.smul_apply, smat, xz, smul_eq_mul, sum_zmod2]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases z with rfl | rfl <;>
    simp [psign]

/-! ## Tensor powers -/

/-- The tensor product `M 0 ⊗ M 1 ⊗ ⋯ ⊗ M (n-1)` of `n` single qubit operators,
written in the computational basis indexed by bit strings. -/
def tp {n : ℕ} (M : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  fun a b => ∏ q, M q (a q) (b q)

lemma tp_mul {n : ℕ} (M N : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    tp M * tp N = tp (fun q => M q * N q) := by
  ext a c
  simp only [tp, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  exact (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))
    (fun q j => M q (a q) j * N q j (c q))).symm

lemma tp_one {n : ℕ} : tp (fun _ : Fin n => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [tp]
  · simp only [tp, Matrix.one_apply, if_neg h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [Matrix.one_apply, hq])

lemma tp_conjTranspose {n : ℕ} (M : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    (tp M)ᴴ = tp (fun q => (M q)ᴴ) := by
  ext a b
  simp [tp, Matrix.conjTranspose_apply]

lemma tp_smul {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    tp (fun q => c q • M q) = (∏ q, c q) • tp M := by
  ext a b
  simp [tp, Finset.prod_mul_distrib]

/-- Pointwise commutation relations tensor up. -/
lemma tp_conj {n : ℕ} (A P P' : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) (c : Fin n → ℂ)
    (h : ∀ r, A r * P r = c r • (P' r * A r)) :
    tp A * tp P = (∏ r, c r) • (tp P' * tp A) := by
  rw [tp_mul, tp_mul, ← tp_smul]
  exact congrArg tp (funext h)

lemma prod_update_one {n : ℕ} (q : Fin n) (v : ℂ) :
    ∏ r, Function.update (fun _ : Fin n => (1 : ℂ)) q v r = v := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ q)]
  simp

/-- A gate acting on the single qubit `q`, conjugating a tensor product of Pauli factors. -/
lemma tp_update_conj {n : ℕ} (q : Fin n) (A : Matrix (ZMod 2) (ZMod 2) ℂ)
    (P P' : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) (v : ℂ)
    (hq : A * P q = v • (P' q * A)) (hne : ∀ r, r ≠ q → P' r = P r) :
    tp (Function.update (fun _ => 1) q A) * tp P
      = v • (tp P' * tp (Function.update (fun _ => 1) q A)) := by
  have h := tp_conj (Function.update (fun _ => 1) q A) P P'
    (Function.update (fun _ : Fin n => (1 : ℂ)) q v) ?_
  · rwa [prod_update_one] at h
  · intro r
    by_cases hr : r = q
    · subst hr; simpa using hq
    · simp [Function.update_of_ne hr, hne r hr]

/-! ## Paulis, gates and the tableau update -/

/-- A Pauli operator on `n` qubits in tableau form: a phase in `ZMod 4` together with
the `X`-exponents and `Z`-exponents. -/
structure Pauli (n : ℕ) where
  /-- The power of `i` in front. -/
  s : ZMod 4
  /-- The `X` exponents. -/
  x : Fin n → ZMod 2
  /-- The `Z` exponents. -/
  z : Fin n → ZMod 2

/-- The `2^n × 2^n` matrix of a Pauli operator. -/
noncomputable def pauliMatrix {n : ℕ} (p : Pauli n) : Matrix (Bits n) (Bits n) ℂ :=
  ph p.s • tp (fun q => xz (p.x q) (p.z q))

/-- The `ZMod 2`-valued inner product of two bit strings. -/
def ip {n : ℕ} (u v : Bits n) : ZMod 2 := ∑ q, u q * v q

@[simp] lemma ip_zero_right {n : ℕ} (u : Bits n) : ip u 0 = 0 := by simp [ip]

lemma prod_ite_zero {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (f : Fin n → ℂ) :
    (∏ q, if P q then f q else 0) = if ∀ q, P q then ∏ q, f q else 0 := by
  by_cases h : ∀ q, P q
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun q _ => if_pos (h q)
  · rw [if_neg h]
    obtain ⟨q, hq⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

lemma pauliMatrix_apply {n : ℕ} (p : Pauli n) (a b : Bits n) :
    pauliMatrix p a b = ph p.s * (if a = b + p.x then psign (ip p.z b) else 0) := by
  simp only [pauliMatrix, Matrix.smul_apply, smul_eq_mul, tp, xz]
  congr 1
  rw [prod_ite_zero (fun q => a q = b q + p.x q) (fun q => psign (p.z q * b q))]
  congr 1
  · simp only [eq_iff_iff]
    constructor
    · intro h; funext q; simpa using h q
    · intro h q; rw [h]; simp
  · rw [ip, psign_sum]

/-- The Clifford generators: Hadamard, phase gate, controlled-`Z`. -/
inductive Gate (n : ℕ)
  | H : Fin n → Gate n
  | S : Fin n → Gate n
  | CZ : Fin n → Fin n → Gate n

/-- The unitary matrix of a Clifford generator. -/
noncomputable def gateMatrix {n : ℕ} : Gate n → Matrix (Bits n) (Bits n) ℂ
  | .H q => tp (Function.update (fun _ => 1) q hmat)
  | .S q => tp (Function.update (fun _ => 1) q smat)
  | .CZ c t => Matrix.diagonal (fun a => psign (a c * a t))

/-- The classical (tableau) update rule associated with a Clifford generator.
Only a bounded number of entries of the tableau row are touched. -/
def gateUpdate {n : ℕ} : Gate n → Pauli n → Pauli n
  | .H q => fun p =>
      ⟨p.s + 2 * lift2 (p.x q * p.z q), Function.update p.x q (p.z q),
        Function.update p.z q (p.x q)⟩
  | .S q => fun p => ⟨p.s + lift2 (p.x q), p.x, Function.update p.z q (p.x q + p.z q)⟩
  | .CZ c t => fun p =>
      ⟨p.s + 2 * lift2 (p.x c * p.x t), p.x,
        fun r => p.z r + (if r = t then p.x c else 0) + (if r = c then p.x t else 0)⟩

/-- The qubits a gate acts on. -/
def gateSupport {n : ℕ} : Gate n → Finset (Fin n)
  | .H q => {q}
  | .S q => {q}
  | .CZ c t => {c, t}

/-- Number of tableau entries a gate update writes, per tableau row. -/
def gateCost {n : ℕ} : Gate n → ℕ
  | .H _ => 3
  | .S _ => 2
  | .CZ _ _ => 3

/-! ## Single gate correctness -/

lemma gateMatrix_unitary {n : ℕ} (g : Gate n) : gateMatrix g * (gateMatrix g)ᴴ = 1 := by
  cases g with
  | H q =>
      rw [gateMatrix, tp_conjTranspose, tp_mul]
      rw [show (fun r => Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q hmat r *
          (Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q hmat r)ᴴ)
          = fun _ : Fin n => (1 : Matrix (ZMod 2) (ZMod 2) ℂ) from ?_]
      · exact tp_one
      · funext r
        by_cases hr : r = q
        · subst hr; simpa using hmat_unitary
        · simp [Function.update_of_ne hr]
  | S q =>
      rw [gateMatrix, tp_conjTranspose, tp_mul]
      rw [show (fun r => Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q smat r *
          (Function.update (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) q smat r)ᴴ)
          = fun _ : Fin n => (1 : Matrix (ZMod 2) (ZMod 2) ℂ) from ?_]
      · exact tp_one
      · funext r
        by_cases hr : r = q
        · subst hr; simpa using smat_unitary
        · simp [Function.update_of_ne hr]
  | CZ c t =>
      rw [gateMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext a
      simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, Complex.star_def, conj_psign]
      rcases zmod2_cases (a c * a t) with h | h <;> simp [psign, h]

lemma gate_conj {n : ℕ} (g : Gate n) (p : Pauli n) :
    gateMatrix g * pauliMatrix p = pauliMatrix (gateUpdate g p) * gateMatrix g := by
  cases g with
  | H q =>
      have key := tp_update_conj q hmat (fun r => xz (p.x r) (p.z r))
        (fun r => xz ((gateUpdate (Gate.H q) p).x r) ((gateUpdate (Gate.H q) p).z r))
        (psign (p.x q * p.z q)) (by simpa [gateUpdate] using hmat_xz (p.x q) (p.z q))
        (by intro r hr; simp [gateUpdate, Function.update_of_ne hr])
      simp only [gateMatrix, pauliMatrix, Matrix.mul_smul, Matrix.smul_mul, key,
        gateUpdate, ph_add, ph_two_lift]
      rw [smul_smul]
  | S q =>
      have key := tp_update_conj q smat (fun r => xz (p.x r) (p.z r))
        (fun r => xz ((gateUpdate (Gate.S q) p).x r) ((gateUpdate (Gate.S q) p).z r))
        (ph (lift2 (p.x q))) (by simpa [gateUpdate] using smat_xz (p.x q) (p.z q))
        (by intro r hr; simp [gateUpdate, Function.update_of_ne hr])
      simp only [gateMatrix, pauliMatrix, Matrix.mul_smul, Matrix.smul_mul, key,
        gateUpdate, ph_add]
      rw [smul_smul]
  | CZ c t =>
      ext a b
      rw [gateMatrix]
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, pauliMatrix_apply, pauliMatrix_apply]
      have hx : (gateUpdate (Gate.CZ c t) p).x = p.x := rfl
      have hs : (gateUpdate (Gate.CZ c t) p).s = p.s + 2 * lift2 (p.x c * p.x t) := rfl
      have hip : ip (gateUpdate (Gate.CZ c t) p).z b = ip p.z b + p.x c * b t + p.x t * b c := by
        show ip (fun r => p.z r + (if r = t then p.x c else 0) + (if r = c then p.x t else 0)) b
            = _
        simp only [ip, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
          Finset.sum_ite_eq' Finset.univ t (fun _ => p.x c * b t),
          Finset.sum_ite_eq' Finset.univ c (fun _ => p.x t * b c)]
        simp
      rw [hx, hs, hip, ph_add, ph_two_lift]
      by_cases hab : a = b + p.x
      · subst hab
        rw [if_pos rfl, if_pos rfl]
        have hbc : (b + p.x) c = b c + p.x c := rfl
        have hbt : (b + p.x) t = b t + p.x t := rfl
        rw [hbc, hbt]
        rw [show (b c + p.x c) * (b t + p.x t)
            = b c * b t + (b c * p.x t + (p.x c * b t + p.x c * p.x t)) from by ring]
        rw [show ip p.z b + p.x c * b t + p.x t * b c
            = ip p.z b + (p.x c * b t + p.x t * b c) from by ring]
        simp only [psign_add]
        rw [show b c * p.x t = p.x t * b c from mul_comm _ _]
        ring
      · simp [hab]

lemma gateUpdate_local {n : ℕ} (g : Gate n) (p : Pauli n) (r : Fin n) (hr : r ∉ gateSupport g) :
    (gateUpdate g p).x r = p.x r ∧ (gateUpdate g p).z r = p.z r := by
  cases g with
  | H q =>
      have : r ≠ q := by simpa [gateSupport] using hr
      simp [gateUpdate, Function.update_of_ne this]
  | S q =>
      have : r ≠ q := by simpa [gateSupport] using hr
      simp [gateUpdate, Function.update_of_ne this]
  | CZ c t =>
      have h : r ≠ c ∧ r ≠ t := by
        simpa [gateSupport, not_or] using hr
      simp [gateUpdate, h.1, h.2]

/-! ## Circuits -/

/-- The unitary implemented by a circuit (a list of gates applied left to right). -/
noncomputable def circuitMatrix {n : ℕ} : List (Gate n) → Matrix (Bits n) (Bits n) ℂ
  | [] => 1
  | g :: gs => circuitMatrix gs * gateMatrix g

/-- The classical simulation: fold the tableau updates over the circuit. -/
def simulate {n : ℕ} : List (Gate n) → Pauli n → Pauli n
  | [] => id
  | g :: gs => fun p => simulate gs (gateUpdate g p)

/-- The classical cost of updating a full `2n`-row stabilizer tableau along the circuit. -/
def simCost {n : ℕ} (gs : List (Gate n)) : ℕ := 2 * n * (gs.map gateCost).sum

lemma circuitMatrix_unitary {n : ℕ} (gs : List (Gate n)) :
    circuitMatrix gs * (circuitMatrix gs)ᴴ = 1 := by
  induction gs with
  | nil => simp [circuitMatrix]
  | cons g gs ih =>
      rw [circuitMatrix, Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
        Matrix.mul_assoc (circuitMatrix gs), gateMatrix_unitary, Matrix.mul_one, ih]

lemma circuit_conj {n : ℕ} (gs : List (Gate n)) (p : Pauli n) :
    circuitMatrix gs * pauliMatrix p = pauliMatrix (simulate gs p) * circuitMatrix gs := by
  induction gs generalizing p with
  | nil => simp [circuitMatrix, simulate]
  | cons g gs ih =>
      rw [circuitMatrix, simulate, Matrix.mul_assoc, gate_conj g p, ← Matrix.mul_assoc,
        ih (gateUpdate g p), Matrix.mul_assoc]

lemma simCost_le {n : ℕ} (gs : List (Gate n)) : simCost gs ≤ 6 * n * gs.length := by
  have h : (gs.map gateCost).sum ≤ 3 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
        have hg : gateCost g ≤ 3 := by cases g <;> simp [gateCost]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  calc simCost gs = 2 * n * (gs.map gateCost).sum := rfl
    _ ≤ 2 * n * (3 * gs.length) := by exact Nat.mul_le_mul_left _ h
    _ = 6 * n * gs.length := by ring

lemma pauliMatrix_zero_zero {n : ℕ} (p : Pauli n) :
    pauliMatrix p 0 0 = if p.x = 0 then ph p.s else 0 := by
  rw [pauliMatrix_apply]
  by_cases h : p.x = 0
  · rw [if_pos h, if_pos (by rw [h]; simp), ip_zero_right, psign_zero, mul_one]
  · have hcond : ¬ ((0 : Bits n) = 0 + p.x) := by
      simp only [zero_add]
      exact fun hh => h hh.symm
    rw [if_neg hcond, if_neg h, mul_zero]

/-! ## Gottesman–Knill -/

/--
**Gottesman–Knill.** Stabilizer (Clifford) circuits are efficiently classically simulable.

For every circuit `gs` built from the Clifford generators `H`, `S`, `CZ` on `n` qubits and every
Pauli operator `p` (given by its classical tableau data: a phase in `ZMod 4` and `X`/`Z`
exponent vectors):

1. the circuit matrix `circuitMatrix gs` is unitary;
2. *(correctness of the classical simulation)* Heisenberg evolution of `p` by the circuit is
   exactly the Pauli operator whose tableau is computed by the purely classical function
   `simulate gs p`, i.e. `U P U† = pauliMatrix (simulate gs p)`;
3. *(classical readout)* the resulting expectation value in the all-zeros computational basis
   state `|0…0⟩` is read off directly from the simulated tableau;
4. *(efficiency)* the classical cost of the simulation — the number of tableau entries written
   while updating all `2n` rows of a stabilizer tableau along the circuit — is at most
   `6 * n * gs.length`, i.e. linear in the number of qubits and in the circuit size;
5. *(locality)* each gate update only writes to the qubit positions in the gate's support,
   which has at most two elements.
-/
theorem gottesman_knill {n : ℕ} (gs : List (Gate n)) (p : Pauli n) :
    circuitMatrix gs * (circuitMatrix gs)ᴴ = 1 ∧
    circuitMatrix gs * pauliMatrix p * (circuitMatrix gs)ᴴ = pauliMatrix (simulate gs p) ∧
    (circuitMatrix gs * pauliMatrix p * (circuitMatrix gs)ᴴ) 0 0
      = (if (simulate gs p).x = 0 then ph (simulate gs p).s else 0) ∧
    simCost gs ≤ 6 * n * gs.length ∧
    (∀ g ∈ gs, (gateSupport g).card ≤ 2 ∧
      ∀ (q : Pauli n) (r : Fin n), r ∉ gateSupport g →
        (gateUpdate g q).x r = q.x r ∧ (gateUpdate g q).z r = q.z r) := by
  have hconj : circuitMatrix gs * pauliMatrix p * (circuitMatrix gs)ᴴ
      = pauliMatrix (simulate gs p) := by
    rw [circuit_conj, Matrix.mul_assoc, circuitMatrix_unitary, Matrix.mul_one]
  refine ⟨circuitMatrix_unitary gs, hconj, ?_, simCost_le gs, ?_⟩
  · rw [hconj, pauliMatrix_zero_zero]
  · intro g _
    refine ⟨?_, fun q r hr => gateUpdate_local g q r hr⟩
    cases g with
    | H q => simp [gateSupport]
    | S q => simp [gateSupport]
    | CZ c t => exact le_trans (Finset.card_insert_le _ _) (by simp)

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

