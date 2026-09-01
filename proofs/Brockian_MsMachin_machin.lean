import Mathlib
namespace Brockian.MsMachin
/-- Machin's formula: π/4 = 4·arctan(1/5) − arctan(1/239). -/
theorem machin : Real.pi / 4 = 4 * Real.arctan (1 / 5) - Real.arctan (1 / 239) := by
  -- Double-angle: 2·arctan(1/5) = arctan(5/12)
  have h1 : 2 * Real.arctan (1 / 5) = Real.arctan (5 / 12) := by
    rw [Real.two_mul_arctan (by norm_num) (by norm_num)]
    norm_num
  -- Double-angle again: 2·arctan(5/12) = arctan(120/119)
  have h2 : 2 * Real.arctan (5 / 12) = Real.arctan (120 / 119) := by
    rw [Real.two_mul_arctan (by norm_num) (by norm_num)]
    norm_num
  -- Addition formula: arctan(1/239) + arctan(1) = arctan(120/119)
  have h3 : Real.arctan (1 / 239) + Real.arctan 1 = Real.arctan (120 / 119) := by
    rw [Real.arctan_add (by norm_num)]
    norm_num
  have h4 : 4 * Real.arctan (1 / 5) = Real.arctan (120 / 119) := by
    rw [← h2, ← h1]; ring
  rw [h4, ← h3, Real.arctan_one]
  ring
end Brockian.MsMachin

