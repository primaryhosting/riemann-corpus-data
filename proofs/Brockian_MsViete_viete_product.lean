import Mathlib
namespace Brockian.MsViete
/-- Viète's formula (finite truncation identity): the product of nested-radical cosine terms
    telescopes — ∏_{k=1}^{n} cos(x/2^k) = sin x / (2^n · sin(x/2^n)) for sin(x/2^n) ≠ 0. -/
theorem viete_product (x : ℝ) (n : ℕ) (h : Real.sin (x / 2 ^ n) ≠ 0) :
    ∏ k ∈ Finset.Icc 1 n, Real.cos (x / 2 ^ k)
      = Real.sin x / (2 ^ n * Real.sin (x / 2 ^ n)) := by
  -- Key (hypothesis-free) identity, proved by induction via the double-angle formula:
  -- 2^m · sin(x/2^m) · ∏_{k=1}^{m} cos(x/2^k) = sin x.
  have key : ∀ m : ℕ, (2 : ℝ) ^ m * Real.sin (x / 2 ^ m) *
      ∏ k ∈ Finset.Icc 1 m, Real.cos (x / 2 ^ k) = Real.sin x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_Icc_succ_top (by omega)]
      have hx : x / 2 ^ m = 2 * (x / 2 ^ (m + 1)) := by field_simp; ring
      have hsin : Real.sin (x / 2 ^ m)
          = 2 * Real.sin (x / 2 ^ (m + 1)) * Real.cos (x / 2 ^ (m + 1)) := by
        rw [hx, Real.sin_two_mul]
      rw [← ih, hsin]
      ring
  have h2 : ((2 : ℝ) ^ n * Real.sin (x / 2 ^ n)) ≠ 0 := by positivity
  field_simp
  linarith [key n]
end Brockian.MsViete

