import Mathlib
namespace Brockian.MsQrTwo
/-- Second supplement to quadratic reciprocity: 2 is a quadratic residue mod an odd prime p
    iff p ≡ ±1 (mod 8). -/
theorem two_is_qr_iff {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ZMod.exists_sq_eq_two_iff ?_
  rintro rfl
  obtain ⟨k, hk⟩ := hodd
  omega
end Brockian.MsQrTwo

