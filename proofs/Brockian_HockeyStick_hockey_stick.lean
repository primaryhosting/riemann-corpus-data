import Mathlib
namespace Brockian.HockeyStick
/-- The hockey-stick identity: ∑_{i=r}^{n} C(i,r) = C(n+1, r+1). -/
theorem hockey_stick (n r : ℕ) (h : r ≤ n) :
    ∑ i ∈ Finset.Icc r n, Nat.choose i r = Nat.choose (n + 1) (r + 1) := by
  exact Nat.sum_Icc_choose n r
end Brockian.HockeyStick

