import Mathlib

namespace Brockian.HighAssurance.SMTMirror

/-- 1. XOR one-time-pad / stream-cipher involution (crypto core; SMT bitvector theory).
    Decrypting with the same key recovers the message. -/
theorem xor_otp_involution (m k : BitVec 8) : (m ^^^ k) ^^^ k = m := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- 2. Access-control default-deny (boolean logic; SMT bool theory).
    canAccess := inScope || isPriv || isUnowned ; when all three grants are false, access is denied. -/
theorem default_deny_denies (inScope isPriv isUnowned : Bool)
    (h1 : inScope = false) (h2 : isPriv = false) (h3 : isUnowned = false) :
    (inScope || isPriv || isUnowned) = false := by
  simp [h1, h2, h3]

/-- 3a. Unauthorized-write memory frame (array theory; SMT-mirror of memory separation).
    Memory is `Addr → Val`; a guarded write only takes effect when authorized. -/
def guardedWrite (auth : Bool) (a : ℕ) (v : ℕ) (m : ℕ → ℕ) : ℕ → ℕ :=
  fun x => if auth ∧ x = a then v else m x

/-- An unauthorized write (auth = false) leaves every address unchanged. -/
theorem unauth_write_frame (a v : ℕ) (m : ℕ → ℕ) (x : ℕ) :
    guardedWrite false a v m x = m x := by
  simp [guardedWrite]

/-- 3b. Non-vacuity: an authorized write does update the targeted address. -/
theorem auth_write_updates (a v : ℕ) (m : ℕ → ℕ) :
    guardedWrite true a v m a = v := by
  simp [guardedWrite]

end Brockian.HighAssurance.SMTMirror
