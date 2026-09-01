import Mathlib
namespace Brockian.ErdosGinzburgZiv
/-- Erdős–Ginzburg–Ziv: among any 2n−1 elements of ℤ/n, some n of them sum to 0. -/
theorem erdos_ginzburg_ziv (n : ℕ) (hn : 0 < n) (f : Fin (2 * n - 1) → ZMod n) :
    ∃ s : Finset (Fin (2 * n - 1)), s.card = n ∧ ∑ i ∈ s, f i = 0 := by
  obtain ⟨s, -, hs, hsum⟩ :=
    ZMod.erdos_ginzburg_ziv (s := Finset.univ) f (by simp)
  exact ⟨s, hs, hsum⟩
end Brockian.ErdosGinzburgZiv

