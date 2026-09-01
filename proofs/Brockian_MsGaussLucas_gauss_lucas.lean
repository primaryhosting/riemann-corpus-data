import Mathlib
namespace Brockian.MsGaussLucas

open Polynomial

/-- The conjugate of `u⁻¹` is the positive real multiple `(normSq u)⁻¹` of `u`. -/
private lemma conj_inv_eq_normSq_inv_smul (u : ℂ) :
    (starRingEnd ℂ) u⁻¹ = ((Complex.normSq u)⁻¹ : ℝ) • u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · have h : (starRingEnd ℂ) u * u = ((Complex.normSq u : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
    have hcu : (starRingEnd ℂ) u ≠ 0 := by simpa using hu
    have hn : ((Complex.normSq u : ℝ) : ℂ) ≠ 0 := by
      rw [← h]; exact mul_ne_zero hcu hu
    rw [map_inv₀, Complex.real_smul, Complex.ofReal_inv]
    field_simp
    linear_combination -h

/-- Conjugating the relation `∑ (z - r i)⁻¹ = 0` gives a vanishing positively weighted sum. -/
private lemma sum_normSq_inv_smul_eq_zero {n : ℕ} (r : Fin n → ℂ) (z : ℂ)
    (hsum : ∑ i, (z - r i)⁻¹ = 0) :
    ∑ i, ((Complex.normSq (z - r i))⁻¹ : ℝ) • (z - r i) = 0 := by
  have h := congrArg (starRingEnd ℂ) hsum
  rw [map_sum, map_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => (conj_inv_eq_normSq_inv_smul (z - r i)).symm

/-- If `z` is different from all of the points `r i` and the sum of `(z - r i)⁻¹` vanishes,
then `z` lies in the convex hull of the `r i`. -/
private lemma mem_convexHull_of_sum_inv_eq_zero {n : ℕ} (hn : 0 < n) (r : Fin n → ℂ) (z : ℂ)
    (hne : ∀ i, z ≠ r i) (hsum : ∑ i, (z - r i)⁻¹ = 0) :
    z ∈ convexHull ℝ (Set.range r) := by
  classical
  set w : Fin n → ℝ := fun i => (Complex.normSq (z - r i))⁻¹ with hw
  have hwpos : ∀ i, 0 < w i := by
    intro i
    have : z - r i ≠ 0 := sub_ne_zero.mpr (hne i)
    simpa [hw] using inv_pos.mpr (Complex.normSq_pos.mpr this)
  have hW : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ => hwpos i) (Finset.univ_nonempty_iff.mpr
      (Fin.pos_iff_nonempty.mp hn))
  have hzero : ∑ i, w i • (z - r i) = 0 := sum_normSq_inv_smul_eq_zero r z hsum
  have hkey : (Finset.univ : Finset (Fin n)).centerMass w r = z := by
    have h1 : (∑ i, w i) • z = ∑ i, w i • r i := by
      have : (∑ i, w i • z) - (∑ i, w i • r i) = 0 := by
        rw [← Finset.sum_sub_distrib]
        simpa [smul_sub] using hzero
      rw [Finset.sum_smul]
      linear_combination (norm := module) this
    rw [Finset.centerMass, ← h1, inv_smul_smul₀ (ne_of_gt hW)]
  rw [← hkey]
  exact Finset.centerMass_mem_convexHull _ (fun i _ => (hwpos i).le) hW
    (fun i _ => Set.mem_range_self i)

/-- Every nonzero complex polynomial factors as a constant times a product of linear factors,
indexed by `Fin p.natDegree`. -/
private lemma exists_linear_factorization (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ (a : ℂ) (r : Fin p.natDegree → ℂ), a ≠ 0 ∧ p = C a * ∏ i, (X - C (r i)) := by
  induction d : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn
      use p.coeff 0
      have hne : p.coeff 0 ≠ 0 := by
        intro h
        apply hp
        rw [Polynomial.eq_C_of_natDegree_eq_zero d]
        simp [h]
      use fun i => 0
      simp [hne]
      exact Polynomial.eq_C_of_natDegree_eq_zero d
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hdeg : 0 < p.natDegree := by rw [d]; exact hn'
      -- Find a root of p
      have hdeg' : p.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.mp hdeg)
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg'
      -- (X - r) divides p
      have hdvd : (X - C r) ∣ p := dvd_iff_isRoot.mpr hr
      obtain ⟨q, hq⟩ := hdvd
      -- q ≠ 0
      have hq0 : q ≠ 0 := by
        intro hqz
        rw [hq, hqz, mul_zero] at hp
        exact hp rfl
      -- natDegree q = n - 1
      have hqdeg : q.natDegree = n - 1 := by
        have : p.natDegree = (X - C r).natDegree + q.natDegree := by
          rw [hq]; exact natDegree_mul (X_sub_C_ne_zero r) hq0
        rw [natDegree_X_sub_C] at this
        omega
      -- Apply inductive hypothesis to q
      have ihq := ih (n - 1) (by omega) q hq0 hqdeg
      obtain ⟨a, s, ha, hs⟩ := ihq
      -- Combine into a factorization for p
      have heq : n = n - 1 + 1 := by omega
      have hinv : n - 1 + 1 = n := by omega
      -- Use n - 1 + 1 = n to work with Fin (n - 1 + 1) directly
      have key : ∃ (a : ℂ) (r' : Fin (n - 1 + 1) → ℂ), a ≠ 0 ∧ (X - C r) * q = C a * ∏ i : Fin (n - 1 + 1), (X - C (r' i)) := by
        use a, Fin.cons r s
        refine ⟨ha, ?_⟩
        rw [hs]
        rw [Fin.prod_univ_succ]
        simp [Fin.cons_zero]
        ring
      obtain ⟨a', r', ha', hr'⟩ := key
      use a', r' ∘ Fin.cast heq
      refine ⟨ha', ?_⟩
      rw [hq, hr']
      congr 1
      symm
      apply Finset.prod_bij (fun i _ => Fin.cast heq i)
      · intro i _; simp
      · intro i₁ _ i₂ _ h; exact Fin.cast_injective heq h
      · intro b _; exact ⟨Fin.cast hinv b, by simp⟩
      · intro i _; simp

/-- Logarithmic derivative identity: if `p = C a * ∏ (X - r i)`, `z` is a root of `p.derivative`
and `z` is not a root of `p`, then `∑ (z - r i)⁻¹ = 0`. -/
private lemma sum_inv_eq_zero_of_isRoot_derivative {n : ℕ} (p : ℂ[X]) (a : ℂ) (ha : a ≠ 0)
    (r : Fin n → ℂ) (hfac : p = C a * ∏ i, (X - C (r i))) (z : ℂ)
    (hz : p.derivative.IsRoot z) (hpz : ¬ p.IsRoot z) :
    ∑ i, (z - r i)⁻¹ = 0 := by
  -- Rewrite using hfac
  rw [hfac] at hz hpz
  simp only [IsRoot, eval_mul, eval_C] at hz hpz
  -- Let P = ∏ (X - r i), so p = a * P and p' = a * P'
  set P : ℂ[X] := ∏ i, (X - C (r i)) with hP
  -- The derivative p' = a * P' (since a is constant)
  rw [Polynomial.derivative_C_mul] at hz
  -- So P'(z) = 0 (since a ≠ 0)
  have hPz : P.eval z ≠ 0 := by
    intro h
    apply hpz
    simp [h]
  have hdPz : (Polynomial.derivative P).eval z = 0 := by
    rw [eval_mul, eval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_left ha
  -- Key identity: (derivative P).eval z = P.eval z * ∑ (z - r i)⁻¹
  have key : ∀ (m : ℕ) (s : Fin m → ℂ) (w : ℂ) (hne : ∀ i, w ≠ s i),
      (Polynomial.derivative (∏ i : Fin m, (X - C (s i)))).eval w =
      (∏ i : Fin m, (X - C (s i))).eval w * ∑ i : Fin m, (w - s i)⁻¹ := by
    intro m
    induction' m with m ih
    · intro s w; simp
    · intro s w hne
      let s' : Fin m → ℂ := fun i => s (Fin.succ i)
      have hne0 : w ≠ s 0 := hne 0
      have hn' : ∀ i : Fin m, w ≠ s' i := fun i => hne i.succ
      have hprod_split : ∏ i : Fin (m + 1), (X - C (s i)) = (X - C (s 0)) * ∏ i : Fin m, (X - C (s' i)) := by
        rw [Fin.prod_univ_succ]
      have hderiv_split : derivative (∏ i : Fin (m + 1), (X - C (s i))) =
          (∏ i : Fin m, (X - C (s' i))) + (X - C (s 0)) * derivative (∏ i : Fin m, (X - C (s' i))) := by
        rw [hprod_split, derivative_mul]
        simp [derivative_sub, derivative_X, derivative_C]
      have hsum_split : ∑ i : Fin (m + 1), (w - s i)⁻¹ = (w - s 0)⁻¹ + ∑ i : Fin m, (w - s' i)⁻¹ := by
        rw [Fin.sum_univ_succ]
      have heval_split : (∏ i : Fin (m + 1), (X - C (s i))).eval w = (w - s 0) * (∏ i : Fin m, (X - C (s' i))).eval w := by
        rw [hprod_split, Polynomial.eval_mul]
        simp
      rw [hderiv_split, Polynomial.eval_add, Polynomial.eval_mul]
      simp only [Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
      rw [heval_split, hsum_split]
      have ih' := ih s' w hn'
      rw [ih']
      field_simp [sub_ne_zero.mpr hne0]
  have hne : ∀ i, z ≠ r i := by
    intro i hi
    apply hpz
    rw [hP]
    simp only [hi]
    simp [Polynomial.eval_prod]
    right
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  have key_applied := key n r z hne
  rw [key_applied] at hdPz
  simp only [mul_eq_zero] at hdPz
  exact hdPz.resolve_left hPz

/-- The Gauss–Lucas theorem: every root of the derivative p' lies in the convex hull of the roots
    of p, for a nonconstant complex polynomial p. -/
theorem gauss_lucas (p : Polynomial ℂ) (hp : 0 < p.degree) (z : ℂ)
    (hz : p.derivative.IsRoot z) :
    z ∈ convexHull ℝ {w : ℂ | p.IsRoot w} := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  by_cases hpz : p.IsRoot z
  · exact subset_convexHull ℝ _ hpz
  · obtain ⟨a, r, ha, hfac⟩ := exists_linear_factorization p hp0
    have hn : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr hp
    have hne : ∀ i, z ≠ r i := by
      intro i hi
      apply hpz
      rw [hfac]
      simp only [IsRoot, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; ring)]
      ring
    have hsum := sum_inv_eq_zero_of_isRoot_derivative p a ha r hfac z hz hpz
    have hmem := mem_convexHull_of_sum_inv_eq_zero hn r z hne hsum
    refine convexHull_mono ?_ hmem
    rintro w ⟨i, rfl⟩
    show p.IsRoot (r i)
    rw [hfac]
    simp only [IsRoot, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)]
    ring

end Brockian.MsGaussLucas

