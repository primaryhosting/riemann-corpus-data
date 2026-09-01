import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

theorem zumkeller_mul_coprime {n m : ℕ} (h : Zumkeller n) (hm : 0 < m)
    (hco : n.Coprime m) : Zumkeller (n * m) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨∅, by simp, by simp⟩
  obtain ⟨S, hSsub, hSsum⟩ := h
  have hSdvd : ∀ d ∈ S, d ∣ n := fun d hd => (Nat.mem_divisors.mp (hSsub hd)).1
  set T : Finset ℕ := (S ×ˢ m.divisors).image (fun p => p.1 * p.2) with hT
  have hinj : ∀ p ∈ S ×ˢ m.divisors, ∀ q ∈ S ×ˢ m.divisors,
      p.1 * p.2 = q.1 * q.2 → p = q := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hEq
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have hbm : b ∣ m := (Nat.mem_divisors.mp hb).1
    have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
    have han : a ∣ n := hSdvd a ha
    have hcn : c ∣ n := hSdvd c hc
    have hEq' : a * b = c * d := hEq
    have hac : a = c := by
      have h1 : a ∣ c :=
        Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.Coprime.coprime_dvd_left han (Nat.Coprime.coprime_dvd_right hdm hco))
          (hEq' ▸ Dvd.intro b rfl)
      have h2 : c ∣ a :=
        Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.Coprime.coprime_dvd_left hcn (Nat.Coprime.coprime_dvd_right hbm hco))
          (hEq' ▸ Dvd.intro d rfl)
      exact Nat.dvd_antisymm h1 h2
    subst hac
    have hapos : 0 < a := Nat.pos_of_dvd_of_pos han hn
    have hbd : b = d := Nat.eq_of_mul_eq_mul_left hapos hEq'
    simp [hbd]
  have hsub : T ⊆ (n * m).divisors := by
    intro x hx
    rw [hT, Finset.mem_image] at hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    rw [Finset.mem_product] at hab
    exact Nat.mem_divisors.mpr
      ⟨mul_dvd_mul (hSdvd a hab.1) (Nat.mem_divisors.mp hab.2).1,
        Nat.mul_ne_zero hn.ne' hm.ne'⟩
  refine ⟨T, hsub, ?_⟩
  have hsumT : ∑ d ∈ T, d = (∑ d ∈ S, d) * (∑ e ∈ m.divisors, e) := by
    rw [hT, Finset.sum_image hinj, Finset.sum_product, Finset.sum_mul_sum]
  rw [hsumT, hco.sum_divisors_mul, ← mul_assoc, hSsum]

end Brockian.ZumkellerNumbers

