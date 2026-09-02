import Mathlib
/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Matrix

namespace QI

/-! ## Computational basis and phases -/

/-- The computational basis of the `n`-qubit Hilbert space is indexed by bit strings. -/
abbrev Qubits (n : ℕ) := Fin n → ZMod 2

/-- The symplectic-friendly bilinear form on bit strings. -/
def dot {n : ℕ} (a b : Qubits n) : ZMod 2 := ∑ i, a i * b i

/-- `iu c = i ^ c` for `c` a phase exponent mod `4`. -/
def iu (c : ZMod 4) : ℂ := Complex.I ^ c.val

/-- The inclusion `ZMod 2 → ZMod 4`, `t ↦ 2t`. -/
def two (t : ZMod 2) : ZMod 4 := (2 * t.val : ℕ)

/-- The sign `(-1) ^ t`. -/
def sgn (t : ZMod 2) : ℂ := iu (two t)

lemma I_pow_mod (k : ℕ) : Complex.I ^ (k % 4) = Complex.I ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k 4]
  rw [pow_add, pow_mul]
  norm_num [Complex.I_pow_four]

@[simp] lemma iu_zero : iu 0 = 1 := by simp [iu]

lemma iu_add (c d : ZMod 4) : iu (c + d) = iu c * iu d := by
  simp only [iu, ZMod.val_add, I_pow_mod, pow_add]

@[simp] lemma iu_two : iu 2 = -1 := by
  show Complex.I ^ (ZMod.val (2 : ZMod 4)) = -1
  norm_num [show ZMod.val (2 : ZMod 4) = 2 from rfl, Complex.I_sq]

lemma two_add (s t : ZMod 2) : two (s + t) = two s + two t := by
  fin_cases s <;> fin_cases t <;> decide

@[simp] lemma two_zero : two 0 = 0 := by decide

@[simp] lemma sgn_zero : sgn 0 = 1 := by simp [sgn]

lemma sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  simp [sgn, two_add, iu_add]

lemma dot_add_right {n : ℕ} (a b c : Qubits n) : dot a (b + c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_add_left {n : ℕ} (a b c : Qubits n) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

@[simp] lemma dot_zero_right {n : ℕ} (a : Qubits n) : dot a 0 = 0 := by simp [dot]

@[simp] lemma dot_zero_left {n : ℕ} (a : Qubits n) : dot 0 a = 0 := by simp [dot]

@[simp] lemma dot_single_right {n : ℕ} (a : Qubits n) (j : Fin n) (t : ZMod 2) :
    dot a (Pi.single j t) = a j * t := by
  simp [dot, Pi.single_apply, Finset.sum_ite_eq']

@[simp] lemma dot_single_left {n : ℕ} (a : Qubits n) (j : Fin n) (t : ZMod 2) :
    dot (Pi.single j t) a = t * a j := by
  simp [dot, Pi.single_apply, Finset.sum_ite_eq']

/-! ## Pauli operators -/

/-- `pauli a b c` is the matrix of `i ^ c * X ^ a * Z ^ b`, acting on the computational basis
by `|x⟩ ↦ i ^ c (-1) ^ (b ⬝ x) |x + a⟩`. -/
def pauli {n : ℕ} (a b : Qubits n) (c : ZMod 4) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y x => if y = x + a then iu c * sgn (dot b x) else 0

lemma pauli_apply {n : ℕ} (a b : Qubits n) (c : ZMod 4) (y x : Qubits n) :
    pauli a b c y x = if y = x + a then iu c * sgn (dot b x) else 0 := rfl

/-- The product law for Pauli operators. -/
lemma pauli_mul {n : ℕ} (a b a' b' : Qubits n) (c c' : ZMod 4) :
    pauli a b c * pauli a' b' c' = pauli (a + a') (b + b') (c + c' + two (dot b a')) := by
  ext y x
  rw [Matrix.mul_apply, Finset.sum_eq_single (x + a')]
  · simp only [pauli_apply]
    by_cases h : y = x + a' + a
    · simp only [sgn, dot_add_right, dot_add_left, iu_add, two_add] at *
      simp [h, show x + (a + a') = x + a' + a by abel]
      ring
    · have h2 : ¬ (y = x + (a + a')) := by
        rw [show x + (a + a') = x + a' + a by abel]; exact h
      simp [h, h2]
  · intro z _ hz
    simp only [pauli_apply, if_neg hz, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] lemma pauli_one {n : ℕ} : pauli (0 : Qubits n) 0 0 = 1 := by
  ext y x
  simp [pauli_apply, Matrix.one_apply]

lemma pauli_phase {n : ℕ} (a b : Qubits n) (c d : ZMod 4) :
    pauli a b (c + d) = iu d • pauli a b c := by
  ext y x
  simp [pauli_apply, iu_add]
  split
  · ring
  · rfl

lemma pauli_neg {n : ℕ} (a b : Qubits n) (c : ZMod 4) :
    pauli a b (c + 2) = - pauli a b c := by
  rw [pauli_phase]; simp

@[simp] lemma qubits_add_self {n : ℕ} (v : Qubits n) : v + v = 0 := by
  ext i
  exact (by decide : ∀ t : ZMod 2, t + t = 0) (v i)

lemma eq_add_comm {n : ℕ} (y x a : Qubits n) : y = x + a ↔ x = y + a := by
  constructor <;> · rintro rfl; rw [add_assoc, qubits_add_self, add_zero]

lemma sgn_eq_ite (t : ZMod 2) : sgn t = if t = 0 then 1 else -1 := by
  fin_cases t <;> simp [sgn, show two 1 = 2 from rfl]

lemma iu_two_eq_sgn (t : ZMod 2) : iu (two t) = sgn t := rfl

@[simp] lemma sgn_mul_self (t : ZMod 2) : sgn t * sgn t = 1 := by
  rw [sgn_eq_ite]; split <;> norm_num

lemma star_sgn (t : ZMod 2) : (starRingEnd ℂ) (sgn t) = sgn t := by
  rw [sgn_eq_ite]; split <;> simp

lemma star_iu (c : ZMod 4) : (starRingEnd ℂ) (iu c) = iu (-c) := by
  fin_cases c <;> simp [iu, show ZMod.val (1 : ZMod 4) = 1 from rfl,
      show ZMod.val (2 : ZMod 4) = 2 from rfl, show ZMod.val (3 : ZMod 4) = 3 from rfl,
      show -(1 : ZMod 4) = 3 from rfl, show -(2 : ZMod 4) = 2 from rfl,
      show -(3 : ZMod 4) = 1 from rfl]

/-- The adjoint of a Pauli operator is again a Pauli operator. -/
lemma pauli_conjTranspose {n : ℕ} (a b : Qubits n) (c : ZMod 4) :
    (pauli a b c)ᴴ = pauli a b (-c + two (dot b a)) := by
  ext y x
  simp only [Matrix.conjTranspose_apply, pauli_apply, RCLike.star_def]
  by_cases h : y = x + a
  · have h' : x = y + a := (eq_add_comm y x a).1 h
    rw [if_pos h, if_pos h', h', map_mul, star_sgn, star_iu, iu_add, dot_add_right, sgn_add,
      iu_two_eq_sgn]
    calc iu (-c) * sgn (dot b y)
        = iu (-c) * sgn (dot b y) * (sgn (dot b a) * sgn (dot b a)) := by
          rw [sgn_mul_self, mul_one]
      _ = iu (-c) * sgn (dot b a) * (sgn (dot b y) * sgn (dot b a)) := by ring
  · have h' : ¬ (x = y + a) := fun hc => h ((eq_add_comm y x a).2 hc)
    rw [if_neg h, if_neg h']
    simp

@[simp] lemma single_apply_self {n : ℕ} (j : Fin n) (t : ZMod 2) :
    (Pi.single j t : Qubits n) j = t := by simp

lemma single_apply_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) (t : ZMod 2) :
    (Pi.single j t : Qubits n) i = 0 := by simp [h]

lemma add_single_add_single {n : ℕ} (v : Qubits n) (j : Fin n) (t : ZMod 2) :
    v + Pi.single j t + Pi.single j t = v := by
  rw [add_assoc, qubits_add_self, add_zero]

lemma zmod2_add_self (t : ZMod 2) : t + t = 0 := by revert t; decide

/-! ## Pauli data (the classical description of a Pauli operator) -/

/-- The classical description of a Pauli operator on `n` qubits: `2n` bits together with a
phase in `ZMod 4`. -/
structure PauliData (n : ℕ) where
  /-- the `X`-part -/
  a : Qubits n
  /-- the `Z`-part -/
  b : Qubits n
  /-- the phase exponent -/
  c : ZMod 4

/-- The operator described by a piece of Pauli data. -/
def PauliData.mat {n : ℕ} (p : PauliData n) : Matrix (Qubits n) (Qubits n) ℂ :=
  pauli p.a p.b p.c

/-- The inclusion `ZMod 2 → ZMod 4`. -/
def one (t : ZMod 2) : ZMod 4 := (t.val : ℕ)

/-- Elementary `X` operator on qubit `j`. -/
def Xg {n : ℕ} (j : Fin n) : Matrix (Qubits n) (Qubits n) ℂ := pauli (Pi.single j 1) 0 0

/-- Elementary `Z` operator on qubit `j`. -/
def Zg {n : ℕ} (j : Fin n) : Matrix (Qubits n) (Qubits n) ℂ := pauli 0 (Pi.single j 1) 0

/-! ## The Clifford generators -/

/-- Generators of the Clifford group: Hadamard, phase gate and controlled-NOT. -/
inductive Gate (n : ℕ)
  | H : Fin n → Gate n
  | S : Fin n → Gate n
  | CX : (j k : Fin n) → j ≠ k → Gate n

/-- The unitary matrix of a Clifford generator, written as a linear combination of Paulis. -/
noncomputable def gateMat {n : ℕ} : Gate n → Matrix (Qubits n) (Qubits n) ℂ
  | .H j => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (Xg j + Zg j)
  | .S j => ((1 + Complex.I) / 2) • (1 : Matrix (Qubits n) (Qubits n) ℂ)
      + ((1 - Complex.I) / 2) • Zg j
  | .CX j k _ => (2⁻¹ : ℂ) • ((1 : Matrix (Qubits n) (Qubits n) ℂ) + Zg j + Xg k - Zg j * Xg k)

/-- The tableau update rule: `step g p` describes `U p U†`. -/
def step {n : ℕ} : Gate n → PauliData n → PauliData n
  | .H j, p => ⟨p.a + Pi.single j (p.a j + p.b j), p.b + Pi.single j (p.a j + p.b j),
      p.c + two (p.a j * p.b j)⟩
  | .S j, p => ⟨p.a, p.b + Pi.single j (p.a j), p.c + one (p.a j)⟩
  | .CX j k _, p => ⟨p.a + Pi.single k (p.a j), p.b + Pi.single j (p.b k), p.c⟩

/-- The adjoint tableau update rule: `stepAdj g p` describes `U† p U`. -/
def stepAdj {n : ℕ} : Gate n → PauliData n → PauliData n
  | .H j, p => ⟨p.a + Pi.single j (p.a j + p.b j), p.b + Pi.single j (p.a j + p.b j),
      p.c + two (p.a j * p.b j)⟩
  | .S j, p => ⟨p.a, p.b + Pi.single j (p.a j), p.c - one (p.a j)⟩
  | .CX j k _, p => ⟨p.a + Pi.single k (p.a j), p.b + Pi.single j (p.b k), p.c⟩

/-- The qubits a gate acts on. -/
def Gate.qubits {n : ℕ} : Gate n → Finset (Fin n)
  | .H j => {j}
  | .S j => {j}
  | .CX j k _ => {j, k}

/-! ## Unitarity and the conjugation rules -/

lemma two_one : two 1 = 2 := rfl

lemma pauli_two_eq_neg {n : ℕ} (a b : Qubits n) : pauli a b 2 = - pauli a b 0 := by
  simpa using pauli_neg a b 0

@[simp] lemma Xg_conjTranspose {n : ℕ} (j : Fin n) : (Xg j)ᴴ = Xg j := by
  rw [Xg, pauli_conjTranspose]; simp

@[simp] lemma Zg_conjTranspose {n : ℕ} (j : Fin n) : (Zg j)ᴴ = Zg j := by
  rw [Zg, pauli_conjTranspose]; simp

@[simp] lemma Xg_mul_Xg {n : ℕ} (j : Fin n) : Xg j * Xg j = 1 := by
  rw [Xg, pauli_mul]; simp

@[simp] lemma Zg_mul_Zg {n : ℕ} (j : Fin n) : Zg j * Zg j = 1 := by
  rw [Zg, pauli_mul]; simp

lemma Xg_mul_Zg {n : ℕ} (j : Fin n) :
    Xg j * Zg j = pauli (Pi.single j 1) (Pi.single j 1) 0 := by
  rw [Xg, Zg, pauli_mul]; simp

lemma Zg_mul_Xg {n : ℕ} (j : Fin n) :
    Zg j * Xg j = - pauli (Pi.single j 1) (Pi.single j 1) 0 := by
  rw [Zg, Xg, pauli_mul]; simp [two_one, pauli_two_eq_neg]

lemma sqrtTwo_inv_sq : ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 2⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma gate_unitary {n : ℕ} (g : Gate n) : (gateMat g)ᴴ * gateMat g = 1 := by
  cases g with
  | H j =>
      have hsq : (Xg j + Zg j) * (Xg j + Zg j)
          = (2 : ℂ) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
        rw [add_mul, mul_add, mul_add, Xg_mul_Xg, Zg_mul_Zg, Xg_mul_Zg, Zg_mul_Xg]
        module
      simp only [gateMat, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Xg_conjTranspose, Zg_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul,
        RCLike.star_def, Complex.conj_ofReal]
      rw [show ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2)
          = (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))) * 2 by ring,
        sqrtTwo_inv_sq]
      norm_num
  | S j =>
      have hα : star ((1 + Complex.I) / 2 : ℂ) = (1 - Complex.I) / 2 := by
        rw [Complex.ext_iff]; norm_num
      have hβ : star ((1 - Complex.I) / 2 : ℂ) = (1 + Complex.I) / 2 := by
        rw [Complex.ext_iff]; norm_num
      simp only [gateMat, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, Zg_conjTranspose, hα, hβ, add_mul, mul_add,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Zg_mul_Zg, smul_smul]
      rw [show ((1 - Complex.I) / 2 * ((1 + Complex.I) / 2)) = 2⁻¹ by
            rw [Complex.ext_iff]; norm_num,
        show ((1 + Complex.I) / 2 * ((1 - Complex.I) / 2)) = 2⁻¹ by
            rw [Complex.ext_iff]; norm_num,
        show ((1 - Complex.I) / 2 * ((1 - Complex.I) / 2)) = -(Complex.I / 2) by
            rw [Complex.ext_iff]; norm_num [Complex.I_sq],
        show ((1 + Complex.I) / 2 * ((1 + Complex.I) / 2)) = Complex.I / 2 by
            rw [Complex.ext_iff]; norm_num [Complex.I_sq]]
      module
  | CX j k hjk =>
      have hW : Zg j * Xg k = pauli (Pi.single k 1) (Pi.single j 1) 0 := by
        rw [Zg, Xg, pauli_mul]; simp [single_apply_ne hjk.symm]
      have hcomm : Xg k * Zg j = Zg j * Xg k := by
        rw [hW, Xg, Zg, pauli_mul]; simp
      have hsq : ((1 : Matrix (Qubits n) (Qubits n) ℂ) + Zg j + Xg k - Zg j * Xg k)
          * ((1 : Matrix (Qubits n) (Qubits n) ℂ) + Zg j + Xg k - Zg j * Xg k)
          = (4 : ℂ) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
        rw [hW, Xg, Zg]
        simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, pauli_mul]
        simp only [dot_single_right, dot_zero_right, single_apply_ne hjk.symm, Pi.zero_apply,
          mul_one, two_zero, add_zero, zero_add, qubits_add_self, pauli_one]
        module
      simp only [gateMat, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Xg_conjTranspose, Zg_conjTranspose, hcomm, Matrix.smul_mul, Matrix.mul_smul, hsq,
        smul_smul, RCLike.star_def, map_inv₀, Complex.conj_ofNat]
      norm_num

lemma gate_unitary' {n : ℕ} (g : Gate n) : gateMat g * (gateMat g)ᴴ = 1 :=
  mul_eq_one_comm.1 (gate_unitary g)

lemma step_stepAdj {n : ℕ} (g : Gate n) (p : PauliData n) : step g (stepAdj g p) = p := by
  obtain ⟨a, b, c⟩ := p
  cases g with
  | H j =>
      have hs : a j + (a j + b j) = b j := by
        rw [← add_assoc, zmod2_add_self, zero_add]
      have ht : b j + (a j + b j) = a j := by
        rw [add_comm (a j) (b j), ← add_assoc, zmod2_add_self, zero_add]
      simp only [step, stepAdj, Pi.add_apply, single_apply_self, hs, ht]
      rw [PauliData.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · rw [add_comm (b j) (a j)]; exact add_single_add_single a j _
      · rw [add_comm (b j) (a j)]; exact add_single_add_single b j _
      · rw [mul_comm (b j) (a j), add_assoc, ← two_add, zmod2_add_self, two_zero, add_zero]
  | S j =>
      simp only [step, stepAdj]
      rw [PauliData.mk.injEq]
      exact ⟨rfl, add_single_add_single b j _, sub_add_cancel c _⟩
  | CX j k hjk =>
      simp only [step, stepAdj, Pi.add_apply, single_apply_ne hjk,
        single_apply_ne hjk.symm, add_zero]
      rw [PauliData.mk.injEq]
      exact ⟨add_single_add_single a k _, add_single_add_single b j _, rfl⟩

@[simp] lemma one_zero_eq : one 0 = 0 := rfl

@[simp] lemma one_one_eq : one 1 = 1 := rfl

@[simp] lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

lemma iu_one : iu 1 = Complex.I := by
  show Complex.I ^ (ZMod.val (1 : ZMod 4)) = Complex.I
  norm_num [show ZMod.val (1 : ZMod 4) = 1 from rfl]

/-- The Heisenberg rule: conjugating a Pauli by a Clifford generator produces the Pauli
described by `step`. -/
lemma gate_conj {n : ℕ} (g : Gate n) (p : PauliData n) :
    gateMat g * p.mat = (step g p).mat * gateMat g := by
  obtain ⟨a, b, c⟩ := p
  have hc2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  cases g with
  | H j =>
      simp only [gateMat, step, PauliData.mat, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      simp only [Xg, Zg, add_mul, mul_add, pauli_mul]
      rcases hc2 (a j) with ha | ha <;> rcases hc2 (b j) with hb | hb <;>
        simp only [ha, hb, Pi.add_apply, single_apply_self, dot_single_left, dot_single_right,
          dot_zero_left, dot_zero_right, Pi.single_zero, zmod2_one_add_one, mul_zero, mul_one,
          two_zero, two_one, add_zero, zero_add, pauli_neg, add_single_add_single] <;>
        simp only [add_comm] <;>
        abel
  | S j =>
      have hI1 : (1 - Complex.I) / 2 * Complex.I = (1 + Complex.I) / 2 := by
        rw [Complex.ext_iff]; norm_num
      have hI2 : (1 + Complex.I) / 2 * Complex.I = -((1 - Complex.I) / 2) := by
        rw [Complex.ext_iff]; norm_num
      simp only [gateMat, step, PauliData.mat, Zg, add_mul, mul_add, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, pauli_mul]
      rcases hc2 (a j) with ha | ha <;>
        simp only [ha, dot_single_left, dot_zero_right, Pi.single_zero,
          mul_zero, mul_one, two_zero, two_one, one_zero_eq, one_one_eq,
          add_zero, zero_add, add_single_add_single, pauli_phase, iu_one, iu_two, smul_smul,
          hI1, hI2] <;>
        simp only [add_comm] <;>
        module
  | CX j k hjk =>
      simp only [gateMat, step, PauliData.mat, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      simp only [Xg, Zg, add_mul, sub_mul, mul_add, mul_sub, Matrix.one_mul, Matrix.mul_one,
        pauli_mul]
      rcases hc2 (a j) with ha | ha <;> rcases hc2 (b k) with hb | hb <;>
        simp only [ha, hb, Pi.add_apply, single_apply_ne hjk.symm,
          dot_single_left, dot_single_right, dot_zero_left, dot_zero_right, Pi.single_zero,
          mul_zero, mul_one, two_zero, two_one, add_zero, zero_add, pauli_neg,
          add_single_add_single] <;>
        simp only [add_comm] <;>
        abel

/-- Conjugation of a Pauli by a Clifford generator is the Pauli described by `step`. -/
lemma gate_conj_mat {n : ℕ} (g : Gate n) (p : PauliData n) :
    gateMat g * p.mat * (gateMat g)ᴴ = (step g p).mat := by
  rw [gate_conj, Matrix.mul_assoc, gate_unitary', Matrix.mul_one]

/-- Conjugation by the adjoint of a Clifford generator is described by `stepAdj`. -/
lemma gate_conj_adj_mat {n : ℕ} (g : Gate n) (p : PauliData n) :
    (gateMat g)ᴴ * p.mat * gateMat g = (stepAdj g p).mat := by
  have h := gate_conj_mat g (stepAdj g p)
  rw [step_stepAdj] at h
  rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, gate_unitary, Matrix.mul_one, ← Matrix.mul_assoc,
    gate_unitary, Matrix.one_mul]

/-! ## Circuits -/

/-- The unitary of a circuit; the head of the list is the first gate applied. -/
noncomputable def circMat {n : ℕ} : List (Gate n) → Matrix (Qubits n) (Qubits n) ℂ
  | [] => 1
  | g :: C => circMat C * gateMat g

/-- Forward (Schrödinger) tableau simulation: describes `U p U†`. -/
def simulate {n : ℕ} : List (Gate n) → PauliData n → PauliData n
  | [], p => p
  | g :: C, p => simulate C (step g p)

/-- Heisenberg tableau simulation: describes `U† p U`. -/
def simulateAdj {n : ℕ} : List (Gate n) → PauliData n → PauliData n
  | [], p => p
  | g :: C, p => stepAdj g (simulateAdj C p)

/-- The number of elementary updates performed by the tableau simulation:
at most four per gate (two `X`-bits, two `Z`-bits and the phase). -/
def simCost {n : ℕ} : List (Gate n) → ℕ
  | [] => 0
  | _ :: C => 4 + simCost C

lemma circ_unitary {n : ℕ} (C : List (Gate n)) : (circMat C)ᴴ * circMat C = 1 := by
  induction C with
  | nil => simp [circMat]
  | cons g C ih =>
      simp only [circMat, Matrix.conjTranspose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (circMat C)ᴴ, ih, Matrix.one_mul, gate_unitary]

lemma circ_unitary' {n : ℕ} (C : List (Gate n)) : circMat C * (circMat C)ᴴ = 1 :=
  mul_eq_one_comm.1 (circ_unitary C)

/-- Correctness of the forward tableau simulation. -/
lemma circ_conj_mat {n : ℕ} (C : List (Gate n)) (p : PauliData n) :
    circMat C * p.mat * (circMat C)ᴴ = (simulate C p).mat := by
  induction C generalizing p with
  | nil => simp [circMat, simulate]
  | cons g C ih =>
      simp only [circMat, simulate, Matrix.conjTranspose_mul]
      rw [show circMat C * gateMat g * p.mat * ((gateMat g)ᴴ * (circMat C)ᴴ)
          = circMat C * (gateMat g * p.mat * (gateMat g)ᴴ) * (circMat C)ᴴ by
        simp [Matrix.mul_assoc]]
      rw [gate_conj_mat, ih]

/-- Correctness of the Heisenberg tableau simulation. -/
lemma circ_conj_adj_mat {n : ℕ} (C : List (Gate n)) (p : PauliData n) :
    (circMat C)ᴴ * p.mat * circMat C = (simulateAdj C p).mat := by
  induction C generalizing p with
  | nil => simp [circMat, simulateAdj]
  | cons g C ih =>
      simp only [circMat, simulateAdj, Matrix.conjTranspose_mul]
      rw [show (gateMat g)ᴴ * (circMat C)ᴴ * p.mat * (circMat C * gateMat g)
          = (gateMat g)ᴴ * ((circMat C)ᴴ * p.mat * circMat C) * gateMat g by
        simp [Matrix.mul_assoc]]
      rw [ih, gate_conj_adj_mat]

/-! ## Classical read-out -/

/-- The classically computed expectation value `⟨0…0| P |0…0⟩` of the Pauli described by `p`. -/
def expect {n : ℕ} (p : PauliData n) : ℂ := if p.a = 0 then iu p.c else 0

/-- The all-zeros computational basis state. -/
def zeroState (n : ℕ) : Qubits n → ℂ := fun y => if y = 0 then 1 else 0

/-- The state prepared by a stabilizer circuit from `|0…0⟩`. -/
noncomputable def outState {n : ℕ} (C : List (Gate n)) : Qubits n → ℂ := circMat C *ᵥ zeroState n

lemma expect_eq_entry {n : ℕ} (p : PauliData n) : p.mat 0 0 = expect p := by
  simp [PauliData.mat, pauli_apply, expect, eq_comm]

lemma zeroState_entry {n : ℕ} (M : Matrix (Qubits n) (Qubits n) ℂ) :
    star (zeroState n) ⬝ᵥ (M *ᵥ zeroState n) = M 0 0 := by
  simp [dotProduct, Matrix.mulVec, zeroState, ite_mul, mul_ite]

lemma expectation_eq {n : ℕ} (C : List (Gate n)) (p : PauliData n) :
    star (outState C) ⬝ᵥ (p.mat *ᵥ outState C) = expect (simulateAdj C p) := by
  rw [outState, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, circ_conj_adj_mat, zeroState_entry, expect_eq_entry]

/-! ## Locality and cost of the simulation -/

lemma stepAdj_local {n : ℕ} (g : Gate n) (p : PauliData n) (i : Fin n) (hi : i ∉ g.qubits) :
    (stepAdj g p).a i = p.a i ∧ (stepAdj g p).b i = p.b i := by
  cases g with
  | H j =>
      simp only [Gate.qubits, Finset.mem_singleton] at hi
      simp [stepAdj, single_apply_ne hi]
  | S j =>
      simp only [Gate.qubits, Finset.mem_singleton] at hi
      simp [stepAdj, single_apply_ne hi]
  | CX j k hjk =>
      simp only [Gate.qubits, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [stepAdj, single_apply_ne hi.1, single_apply_ne hi.2]

lemma gate_qubits_card {n : ℕ} (g : Gate n) : g.qubits.card ≤ 2 := by
  cases g with
  | H j => simp [Gate.qubits]
  | S j => simp [Gate.qubits]
  | CX j k _ => exact le_trans (Finset.card_insert_le _ _) (by simp)

lemma simCost_eq {n : ℕ} (C : List (Gate n)) : simCost C = 4 * C.length := by
  induction C with
  | nil => simp [simCost]
  | cons g C ih => simp [simCost, ih]; ring

/-! ## Sanity checks: the textbook Clifford conjugation relations -/

lemma H_conj_X {n : ℕ} (j : Fin n) :
    gateMat (Gate.H j) * Xg j * (gateMat (Gate.H j))ᴴ = Zg j := by
  have h := gate_conj_mat (Gate.H j) ⟨Pi.single j 1, 0, 0⟩
  simpa [PauliData.mat, step, Xg, Zg] using h

lemma H_conj_Z {n : ℕ} (j : Fin n) :
    gateMat (Gate.H j) * Zg j * (gateMat (Gate.H j))ᴴ = Xg j := by
  have h := gate_conj_mat (Gate.H j) ⟨0, Pi.single j 1, 0⟩
  simpa [PauliData.mat, step, Xg, Zg] using h

/-- `S X S† = Y`, where `Y = i X Z`. -/
lemma S_conj_X {n : ℕ} (j : Fin n) :
    gateMat (Gate.S j) * Xg j * (gateMat (Gate.S j))ᴴ
      = pauli (Pi.single j 1) (Pi.single j 1) 1 := by
  have h := gate_conj_mat (Gate.S j) ⟨Pi.single j 1, 0, 0⟩
  simpa [PauliData.mat, step, Xg] using h

lemma S_conj_Z {n : ℕ} (j : Fin n) :
    gateMat (Gate.S j) * Zg j * (gateMat (Gate.S j))ᴴ = Zg j := by
  have h := gate_conj_mat (Gate.S j) ⟨0, Pi.single j 1, 0⟩
  simpa [PauliData.mat, step, Zg] using h

/-- `CX X_j CX† = X_j X_k`. -/
lemma CX_conj_X {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    gateMat (Gate.CX j k hjk) * Xg j * (gateMat (Gate.CX j k hjk))ᴴ = Xg j * Xg k := by
  have h := gate_conj_mat (Gate.CX j k hjk) ⟨Pi.single j 1, 0, 0⟩
  rw [show Xg j * Xg k = pauli (Pi.single j 1 + Pi.single k 1) 0 0 by
    rw [Xg, Xg, pauli_mul]; simp]
  simpa [PauliData.mat, step, Xg] using h

/-- `CX Z_k CX† = Z_j Z_k`. -/
lemma CX_conj_Z {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    gateMat (Gate.CX j k hjk) * Zg k * (gateMat (Gate.CX j k hjk))ᴴ = Zg j * Zg k := by
  have h := gate_conj_mat (Gate.CX j k hjk) ⟨0, Pi.single k 1, 0⟩
  rw [show Zg j * Zg k = pauli 0 (Pi.single j 1 + Pi.single k 1) 0 by
    rw [Zg, Zg, pauli_mul]; simp]
  simpa [PauliData.mat, step, Zg, add_comm] using h

/-! ## Gottesman–Knill -/

/-- **Gottesman–Knill.**  Stabilizer (Clifford) circuits are efficiently classically simulable.

For a circuit `C` of Clifford generators on `n` qubits and any Pauli observable described by the
classical data `p`:

* `circMat C` is unitary;
* the classical tableau simulation is exactly correct in the Heisenberg picture, i.e. conjugating
  the Pauli operator by the circuit unitary yields the Pauli operator described by the classically
  computed data `simulateAdj C p`;
* the expectation value of the observable in the state `U|0…0⟩` prepared by the circuit is obtained
  from that classical data by the constant-time read-out `expect`;
* the simulation is efficient: it performs `4` elementary updates per gate, each gate only touching
  the (at most two) coordinates of the qubits it acts on — linear in the circuit size, while the
  Hilbert space being simulated has dimension `2 ^ n`. -/
theorem gottesman_knill (n : ℕ) (C : List (Gate n)) (p : PauliData n) :
    ((circMat C)ᴴ * circMat C = 1 ∧ circMat C * (circMat C)ᴴ = 1) ∧
    (circMat C)ᴴ * p.mat * circMat C = (simulateAdj C p).mat ∧
    star (outState C) ⬝ᵥ (p.mat *ᵥ outState C) = expect (simulateAdj C p) ∧
    simCost C = 4 * C.length ∧
    (∀ (g : Gate n) (q : PauliData n) (i : Fin n), i ∉ g.qubits →
        (stepAdj g q).a i = q.a i ∧ (stepAdj g q).b i = q.b i) ∧
    (∀ g : Gate n, g.qubits.card ≤ 2) ∧
    Fintype.card (Qubits n) = 2 ^ n :=
  ⟨⟨circ_unitary C, circ_unitary' C⟩, circ_conj_adj_mat C p, expectation_eq C p, simCost_eq C,
    fun g q i hi => stepAdj_local g q i hi, gate_qubits_card, by simp⟩

end QI

