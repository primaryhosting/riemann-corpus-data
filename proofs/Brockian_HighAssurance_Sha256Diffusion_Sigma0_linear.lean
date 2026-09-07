import Mathlib

namespace Brockian.HighAssurance.Sha256Diffusion

/-! ## SHA-256 message-schedule / compression diffusion (FIPS 180-4)

SHA-256 mixes its state with four rotate/shift functions:
  Σ₀(x) = ROTR²  x ⊕ ROTR¹³ x ⊕ ROTR²² x
  Σ₁(x) = ROTR⁶  x ⊕ ROTR¹¹ x ⊕ ROTR²⁵ x
  σ₀(x) = ROTR⁷  x ⊕ ROTR¹⁸ x ⊕ SHR³  x
  σ₁(x) = ROTR¹⁷ x ⊕ ROTR¹⁹ x ⊕ SHR¹⁰ x

Each is **GF(2)-linear**: `f (x ⊕ y) = f x ⊕ f y`.  Linearity is the structural
fact behind the message schedule's diffusion analysis — a genuine, non-trivial
bitvector obligation over rotates and shifts (a real step up from constant-time
selector identities). -/

def rotr (x : BitVec 32) (n : Nat) : BitVec 32 := BitVec.rotateRight x n
def shr  (x : BitVec 32) (n : Nat) : BitVec 32 := x >>> n

private theorem rotr_xor (x y : BitVec 32) (n : Nat) :
    rotr (x ^^^ y) n = rotr x n ^^^ rotr y n := by
  simp only [rotr]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h32 : decide (i < 32) = true := by simp [hi]
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor, h32, Bool.true_and]
  cases decide (i < 32 - n % 32) <;> rfl

private theorem shr_xor (x y : BitVec 32) (n : Nat) :
    shr (x ^^^ y) n = shr x n ^^^ shr y n := by
  simp only [shr]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]

def Sigma0 (x : BitVec 32) : BitVec 32 := rotr x 2  ^^^ rotr x 13 ^^^ rotr x 22
def Sigma1 (x : BitVec 32) : BitVec 32 := rotr x 6  ^^^ rotr x 11 ^^^ rotr x 25
def sigma0 (x : BitVec 32) : BitVec 32 := rotr x 7  ^^^ rotr x 18 ^^^ shr  x 3
def sigma1 (x : BitVec 32) : BitVec 32 := rotr x 17 ^^^ rotr x 19 ^^^ shr  x 10

theorem Sigma0_linear (x y : BitVec 32) : Sigma0 (x ^^^ y) = Sigma0 x ^^^ Sigma0 y := by
  simp only [Sigma0, rotr_xor]; ac_rfl

theorem Sigma1_linear (x y : BitVec 32) : Sigma1 (x ^^^ y) = Sigma1 x ^^^ Sigma1 y := by
  simp only [Sigma1, rotr_xor]; ac_rfl

theorem sigma0_linear (x y : BitVec 32) : sigma0 (x ^^^ y) = sigma0 x ^^^ sigma0 y := by
  simp only [sigma0, rotr_xor, shr_xor]; ac_rfl

theorem sigma1_linear (x y : BitVec 32) : sigma1 (x ^^^ y) = sigma1 x ^^^ sigma1 y := by
  simp only [sigma1, rotr_xor, shr_xor]; ac_rfl

end Brockian.HighAssurance.Sha256Diffusion
