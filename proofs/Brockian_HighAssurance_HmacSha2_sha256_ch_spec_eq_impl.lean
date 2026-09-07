import Mathlib

namespace Brockian.HighAssurance.HmacSha2

/-! ## SHA-256 bitwise round functions (FIPS 180-4)

The SHA-256 compression function is built from two bitwise selectors, `Ch` and
`Maj`.  FIPS 180-4 defines them with XOR; constant-time implementations often use
the OR form.  Proving the two forms equal is a real impl-vs-spec obligation. -/

/-- `Ch x y z = (x ∧ y) ⊕ (¬x ∧ z)` — the FIPS spec form of the SHA-256 "choice"
function, identical to the OR form used by constant-time implementations because
the two masked terms are disjoint. -/
theorem sha256_ch_spec_eq_impl (x y z : BitVec 32) :
    (x &&& y) ^^^ ((~~~x) &&& z) = (x &&& y) ||| ((~~~x) &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h32 : decide (i < 32) = true := by simp [hi]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, h32, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

/-- `Maj x y z = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` — the FIPS spec form of the SHA-256
"majority" function, equal to the bitwise OR form. -/
theorem sha256_maj_spec_eq_impl (x y z : BitVec 32) :
    (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
      = (x &&& y) ||| (x &&& z) ||| (y &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> decide

/-! ## HMAC key padding (RFC 2104 / FIPS 198-1) -/

/-- The difference between the inner and outer padded keys is key-independent:
`(k ⊕ ipad) ⊕ (k ⊕ opad) = ipad ⊕ opad`.  This is the structural fact that lets
HMAC's two hash calls share the same processed key. -/
theorem hmac_key_pad_difference (k ipad opad : BitVec 32) :
    (k ^^^ ipad) ^^^ (k ^^^ opad) = ipad ^^^ opad := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor]
  cases k.getLsbD i <;> cases ipad.getLsbD i <;> cases opad.getLsbD i <;> decide

/-- The HMAC pad constants (`ipad = 0x36`, `opad = 0x5c` per byte) XOR to the fixed
constant `0x6a` per byte, independent of any key. -/
theorem hmac_pad_xor_const :
    (0x36363636 : BitVec 32) ^^^ (0x5c5c5c5c : BitVec 32) = (0x6a6a6a6a : BitVec 32) := by
  decide

/-! ## SHA-256 compression arithmetic -/

/-- The SHA-256 compression step forms `T1 = h ⊞ Σ₁(e) ⊞ Ch ⊞ Kₜ ⊞ Wₜ` with
addition modulo 2³².  That fold is only well-defined because `⊞` (`BitVec` add) is
associative. -/
theorem sha256_compress_add_assoc (a b c : BitVec 32) :
    (a + b) + c = a + (b + c) := by
  rw [BitVec.add_assoc]

end Brockian.HighAssurance.HmacSha2
