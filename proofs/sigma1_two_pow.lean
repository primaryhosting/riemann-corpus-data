import Mathlib

def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def Superperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 (sigma1 n) = 2 * n

/-- `σ(2^k) = 2^(k+1) - 1`. -/
lemma sigma1_two_pow (k : ℕ) : sigma1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigma1
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (n + 1)]
      omega

/-- If `σ(m) = m + 1` then `m` is prime. -/
lemma prime_of_sigma1_eq_succ {m : ℕ} (hm : sigma1 m = m + 1) : Nat.Prime m := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [sigma1] at hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp [sigma1] at hm
  have h2 : 2 ≤ m := by omega
  have hmemsub : ∀ d, d ∣ m → d = 1 ∨ d = m := by
    intro d hd
    by_contra hcon
    push_neg at hcon
    obtain ⟨hd1, hdm⟩ := hcon
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hm0 (Nat.eq_zero_of_zero_dvd hd)
    have hd2 : 2 ≤ d := by omega
    have hsub : ({1, d, m} : Finset ℕ) ⊆ m.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Nat.mem_divisors.mpr ⟨one_dvd m, hm0⟩
      · exact Nat.mem_divisors.mpr ⟨hd, hm0⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hm0⟩
    have hsum : ∑ x ∈ ({1, d, m} : Finset ℕ), x ≤ sigma1 m :=
      Finset.sum_le_sum_of_subset hsub
    have hcard : ∑ x ∈ ({1, d, m} : Finset ℕ), x = 1 + d + m := by
      rw [Finset.sum_insert (by simp [Ne.symm hd1, Ne.symm hm1]), Finset.sum_insert (by simp [hdm]),
        Finset.sum_singleton]
      ring
    omega
  exact Nat.prime_def.mpr ⟨h2, hmemsub⟩

theorem mersenne_prime_of_superperfect_two_pow {k : ℕ}
    (h : Superperfect (2 ^ k)) : Nat.Prime (2 ^ (k + 1) - 1) := by
  obtain ⟨-, h⟩ := h
  rw [sigma1_two_pow k] at h
  apply prime_of_sigma1_eq_succ
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [h, pow_succ 2 k]
  omega

