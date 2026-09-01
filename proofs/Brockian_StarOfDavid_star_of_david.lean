import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/
private lemma choose_add_mul_factorial (a b : ℕ) :
    (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  simpa using h

private lemma choose_mul_fact {a b n : ℕ} (h : n = a + b) :
    n.choose a * a.factorial * b.factorial = n.factorial := by
  subst h; exact choose_add_mul_factorial a b

/-- The product form of the Star of David theorem. -/
private lemma choose_prod_identity (j r : ℕ) :
    (j + r + 1).choose j * (j + r + 2).choose (j + 2) * (j + r + 3).choose (j + 1)
      = (j + r + 1).choose (j + 1) * (j + r + 2).choose j * (j + r + 3).choose (j + 2) := by
  have h1 : (j + r + 1).choose j * j.factorial * (r + 1).factorial = (j + r + 1).factorial :=
    choose_mul_fact (by omega)
  have h2 : (j + r + 2).choose (j + 2) * (j + 2).factorial * r.factorial = (j + r + 2).factorial :=
    choose_mul_fact (by omega)
  have h3 : (j + r + 3).choose (j + 1) * (j + 1).factorial * (r + 2).factorial
      = (j + r + 3).factorial := choose_mul_fact (by omega)
  have h4 : (j + r + 1).choose (j + 1) * (j + 1).factorial * r.factorial = (j + r + 1).factorial :=
    choose_mul_fact (by omega)
  have h5 : (j + r + 2).choose j * j.factorial * (r + 2).factorial = (j + r + 2).factorial :=
    choose_mul_fact (by omega)
  have h6 : (j + r + 3).choose (j + 2) * (j + 2).factorial * (r + 1).factorial
      = (j + r + 3).factorial := choose_mul_fact (by omega)
  set K := j.factorial * (j + 1).factorial * (j + 2).factorial * r.factorial * (r + 1).factorial *
      (r + 2).factorial with hK
  have hKpos : 0 < K := by
    positivity
  refine Nat.eq_of_mul_eq_mul_right hKpos ?_
  have hL : ((j + r + 1).choose j * (j + r + 2).choose (j + 2) * (j + r + 3).choose (j + 1)) * K
      = (j + r + 1).factorial * (j + r + 2).factorial * (j + r + 3).factorial := by
    rw [← h1, ← h2, ← h3, hK]; ring
  have hR : ((j + r + 1).choose (j + 1) * (j + r + 2).choose j * (j + r + 3).choose (j + 2)) * K
      = (j + r + 1).factorial * (j + r + 2).factorial * (j + r + 3).factorial := by
    rw [← h4, ← h5, ← h6, hK]; ring
  rw [hL, hR]

/-- Abstract key step: divisibility of one triple gcd by the other. -/
private lemma star_key {a b c a' b' c' : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (hprod : a * b * c = a' * b' * c')
    (h1 : c' = a + a' + b) (h2 : c = b' + a + a') :
    Nat.gcd (Nat.gcd a b) c ∣ Nat.gcd (Nat.gcd a' b') c' := by
  have hda : Nat.gcd (Nat.gcd a b) c ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left a b)
  have hdb : Nat.gcd (Nat.gcd a b) c ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right a b)
  have hdc : Nat.gcd (Nat.gcd a b) c ∣ c := Nat.gcd_dvd_right _ _
  have hda' : Nat.gcd (Nat.gcd a b) c ∣ a' := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p e hp hpe
    by_contra hcon
    have hpa : p ^ e ∣ a := hpe.trans hda
    have hpb : p ^ e ∣ b := hpe.trans hdb
    have hpc : p ^ e ∣ c := hpe.trans hdc
    have hnb' : ¬ p ^ e ∣ b' := by
      intro h
      refine hcon ?_
      have hsub : c - (b' + a) = a' := by omega
      exact hsub ▸ Nat.dvd_sub hpc (dvd_add h hpa)
    have hnc' : ¬ p ^ e ∣ c' := by
      intro h
      refine hcon ?_
      have hsub : c' - (a + b) = a' := by omega
      exact hsub ▸ Nat.dvd_sub h (dvd_add hpa hpb)
    have hA : e ≤ a.factorization p := (hp.pow_dvd_iff_le_factorization ha).1 hpa
    have hB : e ≤ b.factorization p := (hp.pow_dvd_iff_le_factorization hb).1 hpb
    have hC : e ≤ c.factorization p := (hp.pow_dvd_iff_le_factorization hc).1 hpc
    have hA' : a'.factorization p < e := by
      by_contra hle
      exact hcon ((hp.pow_dvd_iff_le_factorization ha').2 (not_lt.1 hle))
    have hB' : b'.factorization p < e := by
      by_contra hle
      exact hnb' ((hp.pow_dvd_iff_le_factorization hb').2 (not_lt.1 hle))
    have hC' : c'.factorization p < e := by
      by_contra hle
      exact hnc' ((hp.pow_dvd_iff_le_factorization hc').2 (not_lt.1 hle))
    have hfl : (a * b * c).factorization p
        = a.factorization p + b.factorization p + c.factorization p := by
      rw [Nat.factorization_mul (mul_ne_zero ha hb) hc, Nat.factorization_mul ha hb]
      simp
    have hfr : (a' * b' * c').factorization p
        = a'.factorization p + b'.factorization p + c'.factorization p := by
      rw [Nat.factorization_mul (mul_ne_zero ha' hb') hc', Nat.factorization_mul ha' hb']
      simp
    rw [hprod, hfr] at hfl
    omega
  have hdb' : Nat.gcd (Nat.gcd a b) c ∣ b' := by
    have hsub : c - (a + a') = b' := by omega
    exact hsub ▸ Nat.dvd_sub hdc (dvd_add hda hda')
  have hdc' : Nat.gcd (Nat.gcd a b) c ∣ c' := by
    rw [h1]; exact dvd_add (dvd_add hda hda') hdb
  exact Nat.dvd_gcd (Nat.dvd_gcd hda' hdb') hdc'

/-- Abstract form of the Star of David theorem. -/
private lemma star_abstract {a b c a' b' c' : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (hprod : a * b * c = a' * b' * c')
    (h1 : c' = a + a' + b) (h2 : c = b' + a + a') :
    Nat.gcd (Nat.gcd a b) c = Nat.gcd (Nat.gcd a' b') c' :=
  Nat.dvd_antisymm (star_key ha hb hc ha' hb' hc' hprod h1 h2)
    (star_key ha' hb' hc' ha hb hc hprod.symm (by omega) (by omega))

/-- The Star of David theorem: the two alternating triples of binomial coefficients surrounding
    an entry of Pascal's triangle have equal gcd. -/
theorem star_of_david (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Nat.gcd (Nat.gcd (Nat.choose (n - 1) (k - 1)) (Nat.choose n (k + 1))) (Nat.choose (n + 1) k)
      = Nat.gcd (Nat.gcd (Nat.choose (n - 1) k) (Nat.choose n (k - 1))) (Nat.choose (n + 1) (k + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases eq_or_lt_of_le hkn with heq | hlt
  · subst heq
    simp [Nat.choose_succ_self]
  · obtain ⟨r, rfl⟩ : ∃ r, n = j + r + 2 := ⟨n - j - 2, by omega⟩
    have e1 : j + r + 2 - 1 = j + r + 1 := by omega
    have e2 : j + 1 - 1 = j := by omega
    have e3 : j + r + 2 + 1 = j + r + 3 := by omega
    rw [e1, e2, e3]
    show Nat.gcd (Nat.gcd ((j + r + 1).choose j) ((j + r + 2).choose (j + 2)))
        ((j + r + 3).choose (j + 1))
      = Nat.gcd (Nat.gcd ((j + r + 1).choose (j + 1)) ((j + r + 2).choose j))
        ((j + r + 3).choose (j + 2))
    -- Pascal relations
    have hZ : (j + r + 2).choose (j + 1) = (j + r + 1).choose j + (j + r + 1).choose (j + 1) :=
      Nat.choose_succ_succ (j + r + 1) j
    have hC' : (j + r + 3).choose (j + 2)
        = (j + r + 1).choose j + (j + r + 1).choose (j + 1) + (j + r + 2).choose (j + 2) := by
      rw [← hZ]; exact Nat.choose_succ_succ (j + r + 2) (j + 1)
    have hCC : (j + r + 3).choose (j + 1)
        = (j + r + 2).choose j + (j + r + 1).choose j + (j + r + 1).choose (j + 1) := by
      have h : (j + r + 3).choose (j + 1) = (j + r + 2).choose j + (j + r + 2).choose (j + 1) :=
        Nat.choose_succ_succ (j + r + 2) j
      omega
    exact star_abstract (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
      (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
      (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
      (choose_prod_identity j r) hC' hCC

end Brockian.StarOfDavid

