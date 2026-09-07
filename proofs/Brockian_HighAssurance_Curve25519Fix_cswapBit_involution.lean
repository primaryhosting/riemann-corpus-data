import Mathlib

namespace Brockian.HighAssurance.Curve25519Fix

/-! ## F0, formalized — the corrected Curve25519 `cswap`

Audit finding F0 (`cryptol-specs/Common/EC/Curve25519.cry:349`): the stated
`property cswapTrue y x = y > 0 ==> cswap y (cswap y x) == x` is FALSE, because the
masked constant-time `cswap` computes `mask = 0 - y`, a valid select-mask (all-ones
or zero) only for `y ∈ {0,1}`; the property guards `y > 0`.  The fix retypes the
selector `y : [255]` to a single bit `y : [1]` / guards `elem y [0,1]`.

We verify the corrected property: with a bit-typed selector the mask is a proper
select-mask, and `cswap` genuinely swaps and is an involution — and the wide mask
`0 - y` is a valid select-mask *exactly* when `y ∈ {0,1}`, precisely the guard the
fix restores. -/

/-- Constant-time conditional swap with a BIT-typed selector (the fix).  `mask` is
all-ones when the bit is set, zero otherwise. -/
def cswapBit (bit : Bool) (a b : BitVec 32) : BitVec 32 × BitVec 32 :=
  let mask : BitVec 32 := if bit then BitVec.allOnes 32 else 0
  let t := mask &&& (a ^^^ b)
  (a ^^^ t, b ^^^ t)

/-- With the bit set, the corrected cswap actually swaps the pair. -/
theorem cswapBit_true (a b : BitVec 32) : cswapBit true a b = (b, a) := by
  simp only [cswapBit, if_true, Prod.mk.injEq]
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h32 : decide (i < 32) = true := by simp [hi]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, h32,
      Bool.true_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> decide

/-- With the bit clear, the corrected cswap is the identity. -/
theorem cswapBit_false (a b : BitVec 32) : cswapBit false a b = (a, b) := by
  simp [cswapBit]

/-- The corrected cswap is an involution for BOTH selector values — the property
`cswapTrue` intended, now actually true. -/
theorem cswapBit_involution (bit : Bool) (a b : BitVec 32) :
    cswapBit bit (cswapBit bit a b).1 (cswapBit bit a b).2 = (a, b) := by
  simp only [cswapBit, Prod.mk.injEq]
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
    cases (if bit then BitVec.allOnes 32 else 0 : BitVec 32).getLsbD i <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> decide

/-- F0's condition, formalized: the wide-selector mask `0 - y` is a valid
constant-time select-mask (all-ones or zero) exactly when `y ∈ {0,1}` — precisely
the `elem y [0,1]` guard the fix restores. -/
theorem neg_mask_valid_iff (y : BitVec 32) :
    ((0 : BitVec 32) - y = 0 ∨ (0 : BitVec 32) - y = BitVec.allOnes 32)
      ↔ (y = 0 ∨ y = 1) := by
  have hone : (BitVec.allOnes 32) = (-1 : BitVec 32) := by decide
  rw [hone, zero_sub, neg_eq_zero, neg_eq_iff_eq_neg]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; decide)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; decide)

end Brockian.HighAssurance.Curve25519Fix
