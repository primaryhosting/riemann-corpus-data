import Mathlib

namespace Brockian.HighAssurance.ChaChaQR

abbrev W := BitVec 32

/-- Rotate-cancel: a left rotate undone by a right rotate of the same amount. -/
theorem rotr_rotl (x : W) (n : Nat) (hn : n < 32) :
    (x.rotateLeft n).rotateRight n = x := by
  have hmod : n % 32 = n := Nat.mod_eq_of_lt hn
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, hmod]
  by_cases h1 : i < 32 - n <;>
    by_cases h3 : n + i < 32 <;>
    by_cases h4 : i - (32 - n) < n <;>
    simp_all [Bool.cond_decide] <;>
    (try congr 1) <;> omega

/-- xor self-cancel. -/
private theorem xor_cancel (x y : W) : (x ^^^ y) ^^^ y = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The ChaCha20 quarter-round (RFC 8439): four rounds of modular add, xor, and
fixed left-rotate over a 128-bit state. -/
def QR (a b c d : W) : W × W × W × W :=
  let a := a + b
  let d := (d ^^^ a).rotateLeft 16
  let c := c + d
  let b := (b ^^^ c).rotateLeft 12
  let a := a + b
  let d := (d ^^^ a).rotateLeft 8
  let c := c + d
  let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- The inverse of the quarter-round: each micro-step run backwards (right-rotate,
xor, subtract). -/
def QRinv (a b c d : W) : W × W × W × W :=
  let b1 := (b.rotateRight 7) ^^^ c
  let c1 := c - d
  let d1 := (d.rotateRight 8) ^^^ a
  let a1 := a - b1
  let b0 := (b1.rotateRight 12) ^^^ c1
  let c0 := c1 - d1
  let d0 := (d1.rotateRight 16) ^^^ a1
  let a0 := a1 - b0
  (a0, b0, c0, d0)

/-- **The quarter-round is invertible.**  `QRinv` recovers the input from the
output — every micro-step cancels: right-rotate undoes left-rotate, xor undoes xor,
subtract undoes add. -/
theorem QR_left_inverse (a b c d : W) :
    (fun p : W × W × W × W => QRinv p.1 p.2.1 p.2.2.1 p.2.2.2) (QR a b c d) = (a, b, c, d) := by
  simp only [QR, QRinv]
  rw [rotr_rotl _ 7 (by norm_num), rotr_rotl _ 8 (by norm_num)]
  simp only [xor_cancel]
  rw [rotr_rotl _ 12 (by norm_num), rotr_rotl _ 16 (by norm_num)]
  simp only [xor_cancel, add_sub_cancel_right, add_sub_cancel_left]

/-- **Hence the quarter-round is injective** — a bijection on the 128-bit state. -/
theorem QR_injective : Function.Injective (fun p : W × W × W × W => QR p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hli : Function.LeftInverse
      (fun p : W × W × W × W => QRinv p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p : W × W × W × W => QR p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    intro p
    obtain ⟨a, b, c, d⟩ := p
    exact QR_left_inverse a b c d
  exact hli.injective

end Brockian.HighAssurance.ChaChaQR
