import Mathlib
namespace Brockian.MsWilsonPrimePower

open Finset

/-- If an odd prime power `p ^ k` divides `(a - 1) * (a + 1)`, then it divides one of the two
factors, since `p` cannot divide both `a - 1` and `a + 1`. -/
private lemma prime_pow_dvd_of_dvd_pred_mul_succ (p k : ℕ) (hp : p.Prime) (hodd : Odd p) (a : ℤ)
    (h : ((p : ℤ) ^ k) ∣ (a - 1) * (a + 1)) :
    ((p : ℤ) ^ k) ∣ (a - 1) ∨ ((p : ℤ) ^ k) ∣ (a + 1) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hd : (p : ℤ) ∣ (a + 1)
  · right
    have hnd : ¬ (p : ℤ) ∣ (a - 1) := by
      intro h1
      have h2 : (p : ℤ) ∣ 2 := by simpa using dvd_sub hd h1
      have hp2 : p ∣ 2 := by exact_mod_cast h2
      have hpe : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
      rw [hpe] at hodd
      simp [Nat.odd_iff] at hodd
    have hcop : IsCoprime ((p : ℤ) ^ k) (a - 1) :=
      IsCoprime.pow_left ((hpi.coprime_iff_not_dvd).mpr hnd)
    have h' : ((p : ℤ) ^ k) ∣ (a + 1) * (a - 1) := by rw [mul_comm]; exact h
    exact hcop.dvd_of_dvd_mul_right h'
  · left
    have hcop : IsCoprime ((p : ℤ) ^ k) (a + 1) :=
      IsCoprime.pow_left ((hpi.coprime_iff_not_dvd).mpr hd)
    exact hcop.dvd_of_dvd_mul_right h

/-- For an odd prime `p`, the only square roots of `1` in `ZMod (p ^ k)` are `±1`. -/
private lemma units_sq_eq_one (p k : ℕ) (hp : p.Prime) (hodd : Odd p)
    (x : (ZMod (p ^ k))ˣ) (hx : x * x = 1) : x = 1 ∨ x = -1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  set y : ZMod (p ^ k) := (x : ZMod (p ^ k)) with hy
  have hy2 : y * y = 1 := by
    simpa using congrArg (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k))) hx
  set a : ℤ := (y.val : ℤ) with ha
  have hya : ((a : ℤ) : ZMod (p ^ k)) = y := by simp [ha]
  have hprod : (((a - 1) * (a + 1) : ℤ) : ZMod (p ^ k)) = 0 := by
    push_cast
    rw [hya]
    linear_combination hy2
  have hdvd : ((p : ℤ) ^ k) ∣ (a - 1) * (a + 1) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).mp hprod
    push_cast at h
    exact h
  rcases prime_pow_dvd_of_dvd_pred_mul_succ p k hp hodd a hdvd with h1 | h1
  · left
    have h2 : ((a - 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h1
    push_cast at h2
    rw [hya] at h2
    have h3 : y = 1 := by linear_combination h2
    exact Units.ext (by simpa [hy] using h3)
  · right
    have h2 : ((a + 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h1
    push_cast at h2
    rw [hya] at h2
    have h3 : y = -1 := by linear_combination h2
    exact Units.ext (by simpa [hy] using h3)

/-- The product of all units of `ZMod (p ^ k)`, taken in the unit group, is `-1`.

The product of all elements of a finite abelian group equals the product of its self-inverse
elements; here those are exactly `1` and `-1`. -/
private lemma prod_units_eq_neg_one (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hodd : Odd p) :
    (∏ x : (ZMod (p ^ k))ˣ, x) = -1 := by
  classical
  have hinv : ∀ x : (ZMod (p ^ k))ˣ, x⁻¹ = x → x = 1 ∨ x = -1 := by
    intro x hxx
    refine units_sq_eq_one p k hp hodd x ?_
    nth_rewrite 1 [← hxx]
    exact inv_mul_cancel x
  have h : (∏ x ∈ (univ : Finset (ZMod (p ^ k))ˣ).erase (-1), x) = 1 := by
    refine Finset.prod_involution (fun x _ => x⁻¹) (by simp) ?_ ?_ (by simp)
    · intro a ha ha1 hinva
      rcases hinv a hinva with h1 | h1
      · exact ha1 h1
      · exact (Finset.mem_erase.mp ha).1 h1
    · intro a ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hcon
      exact (Finset.mem_erase.mp ha).1 (by simpa using congrArg (fun y => y⁻¹) hcon)
  rw [← Finset.insert_erase (Finset.mem_univ (-1 : (ZMod (p ^ k))ˣ)),
    Finset.prod_insert (Finset.notMem_erase _ _), h, mul_one]

/-- Gauss's extension of Wilson's theorem: for an odd prime p and k ≥ 1, the product of all
    units of ℤ/(p^k) equals −1.

    (The instance argument `[NeZero (p ^ k)]`, which follows from `hp` and `hk`, is only needed so
    that `ZMod (p ^ k)` is known to be a finite type when the product is elaborated. The hypothesis
    `hk : 0 < k` is kept as stated, although the proof does not need it.) -/
theorem wilson_prime_power (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hodd : Odd p) (hk : 0 < k) :
    (∏ u : (ZMod (p ^ k))ˣ, (u : ZMod (p ^ k))) = -1 := by
  have h := congrArg (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k)))
    (prod_units_eq_neg_one p k hp hodd)
  simpa [Units.coe_prod] using h

end Brockian.MsWilsonPrimePower

