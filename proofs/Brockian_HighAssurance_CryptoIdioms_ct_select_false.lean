import Mathlib

namespace Brockian.HighAssurance.CryptoIdioms

/-- Stream-cipher / one-time-pad involution: encrypting then decrypting with the
same key returns the plaintext. -/
theorem otp_involution (m k : BitVec 32) : (m ^^^ k) ^^^ k = m := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Masking identity: selecting between `a` and `a` yields `a` — the core of
constant-time masking. -/
theorem mask_select_identity (mask a : BitVec 32) :
    (mask &&& a) ||| ((~~~mask) &&& a) = a := by
  rw [← BitVec.and_or_distrib_right, BitVec.or_not_self, BitVec.allOnes_and]

/-- Constant-time conditional select. `mask = all-ones` selects `a`;
`mask = 0` selects `b`. -/
def ctSelect (mask a b : BitVec 32) : BitVec 32 := (mask &&& a) ||| ((~~~mask) &&& b)

theorem ct_select_true  (a b : BitVec 32) : ctSelect (-1 : BitVec 32) a b = a := by
  unfold ctSelect
  bv_decide

theorem ct_select_false (a b : BitVec 32) : ctSelect (0  : BitVec 32) a b = b := by
  unfold ctSelect
  bv_decide

/-- The XOR-swap trick returns the swapped pair. -/
theorem xor_swap (a b : BitVec 32) :
    (((a ^^^ b) ^^^ ((a ^^^ b) ^^^ b)), ((a ^^^ b) ^^^ b)) = (b, a) := by
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end Brockian.HighAssurance.CryptoIdioms
