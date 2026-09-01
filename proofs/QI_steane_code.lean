import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace QI

/-! ## Pauli operators on 7 qubits (modulo phases)

A Pauli operator on `n` qubits, taken modulo phases, is encoded by a pair of
vectors over `ZMod 2`: the `X`-part and the `Z`-part.  Qubit `i` carries
`I, X, Z, Y` according to `(x i, z i) = (0,0), (1,0), (0,1), (1,1)`. -/

/-- Binary vectors of length 7. -/
abbrev V := Fin 7 → ZMod 2

/-- A Pauli operator on 7 qubits, modulo phase: `(X`-part, `Z`-part`)`. -/
abbrev Pauli7 := V × V

/-- Binary inner product. -/
def dot (u v : V) : ZMod 2 := ∑ i, u i * v i

/-- The symplectic form: `sympl E F = 0` iff the Pauli operators `E` and `F` commute. -/
def sympl (E F : Pauli7) : ZMod 2 := dot E.1 F.2 + dot E.2 F.1

/-- The parity-check matrix of the `[7,4,3]` Hamming code: the `i`-th column is the
binary expansion of `i + 1`. -/
def H (r : Fin 3) (i : Fin 7) : ZMod 2 := if Nat.testBit (i.val + 1) r.val then 1 else 0

/-- The six stabilizer generators of the Steane code: three `X`-type generators
`H r` and three `Z`-type generators `H r`. -/
def gen (a : Fin 6) : Pauli7 :=
  if h : a.val < 3 then (H ⟨a.val, h⟩, 0) else (0, H ⟨a.val - 3, by omega⟩)

/-- The error syndrome of a Pauli error: the commutation pattern with the six
stabilizer generators, arranged as the pair (`X`-type syndrome, `Z`-type syndrome). -/
def syndrome (E : Pauli7) : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) :=
  (fun r => dot (H r) E.2, fun r => dot (H r) E.1)

/-- `E` is a single-qubit error: it acts as the identity off some qubit `j`. -/
def SingleQubit (E : Pauli7) : Prop := ∃ j : Fin 7, ∀ i : Fin 7, i ≠ j → E.1 i = 0 ∧ E.2 i = 0

/-- The single-qubit Pauli error acting on qubit `j` with `X`-bit `x` and `Z`-bit `z`. -/
def singleErr (j : Fin 7) (x z : ZMod 2) : Pauli7 :=
  (fun i => if i = j then x else 0, fun i => if i = j then z else 0)

lemma singleQubit_singleErr (j : Fin 7) (x z : ZMod 2) : SingleQubit (singleErr j x z) := by
  refine ⟨j, fun i hi => ?_⟩
  simp [singleErr, hi]

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Every single-qubit error is of the form `singleErr j x z`. -/
lemma SingleQubit.exists_repr {E : Pauli7} (h : SingleQubit E) :
    ∃ (j : Fin 7) (x z : ZMod 2), E = singleErr j x z := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, E.1 j, E.2 j, ?_⟩
  ext i
  · by_cases hi : i = j
    · subst hi; simp [singleErr]
    · simp [singleErr, hi, (hj i hi).1]
  · by_cases hi : i = j
    · subst hi; simp [singleErr]
    · simp [singleErr, hi, (hj i hi).2]

/-- Key finite verification: the syndromes of the single-qubit errors are pairwise
distinct, i.e. the Hamming parity-check columns are nonzero and pairwise different. -/
lemma syndrome_injective_on_singleErr :
    ∀ (j k : Fin 7) (x z x' z' : ZMod 2),
      syndrome (singleErr j x z) = syndrome (singleErr k x' z') →
        singleErr j x z = singleErr k x' z' := by
  decide

/-- The six stabilizer generators pairwise commute. -/
lemma gen_commute : ∀ a b : Fin 6, sympl (gen a) (gen b) = 0 := by decide

/-- The stabilizer generators have trivial syndrome (they fix the code space). -/
lemma syndrome_gen : ∀ a : Fin 6, syndrome (gen a) = (0, 0) := by decide

/-!
## The main theorem

The Steane code corrects an arbitrary single-qubit error:

* its six stabilizer generators pairwise commute, so they define a code space;
* distinct single-qubit Pauli errors have distinct syndromes (the Knill–Laflamme
  condition in nondegenerate stabilizer form);
* consequently there is a recovery map which, given the measured syndrome,
  returns exactly the error that occurred.
-/
theorem steane_code :
    (∀ a b : Fin 6, sympl (gen a) (gen b) = 0) ∧
    (∀ E F : Pauli7, SingleQubit E → SingleQubit F → syndrome E = syndrome F → E = F) ∧
    (∃ R : ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) → Pauli7,
        ∀ E : Pauli7, SingleQubit E → R (syndrome E) = E) := by
  have key : ∀ E F : Pauli7, SingleQubit E → SingleQubit F → syndrome E = syndrome F → E = F := by
    rintro E F hE hF hs
    obtain ⟨j, x, z, rfl⟩ := hE.exists_repr
    obtain ⟨k, x', z', rfl⟩ := hF.exists_repr
    exact syndrome_injective_on_singleErr j k x z x' z' hs
  refine ⟨gen_commute, key, ?_⟩
  classical
  refine ⟨fun s => if h : ∃ E : Pauli7, SingleQubit E ∧ syndrome E = s then h.choose else (0, 0),
    fun E hE => ?_⟩
  have hex : ∃ F : Pauli7, SingleQubit F ∧ syndrome F = syndrome E := ⟨E, hE, rfl⟩
  show (if h : ∃ F : Pauli7, SingleQubit F ∧ syndrome F = syndrome E then h.choose
      else (0, 0)) = E
  rw [dif_pos hex]
  obtain ⟨hF, hsyn⟩ := hex.choose_spec
  exact key _ _ hF hE hsyn

end QI

