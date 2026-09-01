import Mathlib

def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

theorem semiperfect_mul_right {n m : ℕ} (hn : 0 < n) (hm : 1 < m)
    (h : Semiperfect n) : Semiperfect (n * m) := by
  obtain ⟨s, hs, hsum⟩ := h
  rw [Finset.mem_powerset] at hs
  refine ⟨s.image (· * m), Finset.mem_powerset.2 ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hd' := hs hd
    rw [Nat.mem_properDivisors] at hd' ⊢
    exact ⟨mul_dvd_mul_right hd'.1 m, by
      exact Nat.mul_lt_mul_of_lt_of_le hd'.2 le_rfl (by omega)⟩
  · rw [Finset.sum_image
      (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right (by omega) hab),
      ← Finset.sum_mul, hsum]

