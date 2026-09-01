import Mathlib

def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

theorem zumkeller_two_mul_of_odd_zumkeller {n : ℕ} (hodd : Odd n)
    (h : Zumkeller n) : Zumkeller (2 * n) := by
  obtain ⟨S, hS, hsum⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hodd
  -- every divisor of `n` is odd
  have hodd_div : ∀ d ∈ n.divisors, Odd d := by
    intro d hd
    rcases (Nat.mem_divisors.mp hd).1 with ⟨k, rfl⟩
    rcases Nat.even_or_odd d with he | ho
    · exact absurd (he.mul_right k) (Nat.not_even_iff_odd.mpr hodd)
    · exact ho
  -- decomposition of the divisors of `2 * n`
  have hdec : (2 * n).divisors = n.divisors ∪ (n.divisors.image (fun a => 2 * a)) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors, ne_eq,
      Nat.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    constructor
    · rintro ⟨hd, -⟩
      rcases Nat.even_or_odd d with ⟨a, ha⟩ | hdodd
      · right
        refine ⟨a, ⟨?_, hn0⟩, by omega⟩
        have : 2 * a ∣ 2 * n := by rw [show 2 * a = d by omega]; exact hd
        exact (mul_dvd_mul_iff_left (by norm_num : (2:ℕ) ≠ 0)).mp this
      · left
        refine ⟨?_, hn0⟩
        have h2 : ¬ (2 ∣ d) := by
          rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff]
          exact hdodd
        have hcop : Nat.Coprime d 2 :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2 |>.symm
        exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hd)
    · rintro (⟨hd, -⟩ | ⟨a, ⟨ha, -⟩, rfl⟩)
      · exact ⟨hd.mul_left 2, hn0⟩
      · exact ⟨mul_dvd_mul_left 2 ha, hn0⟩
  have hdisj : Disjoint n.divisors (n.divisors.image (fun a => 2 * a)) := by
    rw [Finset.disjoint_right]
    rintro d hd hd'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact (Nat.not_even_iff_odd.mpr (hodd_div _ hd')) ⟨a, by omega⟩
  have hinj : Set.InjOn (fun a => 2 * a) (n.divisors : Set ℕ) := by
    intro x _ y _ hxy; simpa using hxy
  have hsum2 : ∑ d ∈ (2 * n).divisors, d = 3 * ∑ d ∈ n.divisors, d := by
    rw [hdec, Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.mul_sum]
    ring
  -- the witness set
  refine ⟨(n.divisors \ S) ∪ S.image (fun a => 2 * a), ?_, ?_⟩
  · rw [hdec]
    apply Finset.union_subset
    · exact (Finset.sdiff_subset).trans Finset.subset_union_left
    · exact (Finset.image_subset_image hS).trans Finset.subset_union_right
  · have hdisj' : Disjoint (n.divisors \ S) (S.image (fun a => 2 * a)) :=
      (Finset.disjoint_of_subset_right (Finset.image_subset_image hS)
        (Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj))
    have hinj' : Set.InjOn (fun a => 2 * a) (S : Set ℕ) := by
      intro x _ y _ hxy; simpa using hxy
    rw [Finset.sum_union hdisj', Finset.sum_image hinj', hsum2, ← Finset.mul_sum]
    have hsd : (∑ d ∈ n.divisors \ S, d) + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff hS
    omega

