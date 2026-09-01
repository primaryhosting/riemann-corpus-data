import Mathlib

namespace Brockian.MasonStothers

open Polynomial UniqueFactorizationMonoid

/-
The statement as originally given (over an arbitrary field `K`, with the number of distinct
roots taken in `K` itself) is false: over `K = ℚ`, take `a = X ^ 2 + 1`, `b = 1`,
`c = X ^ 2 + 2`.  These are coprime, `a + b = c`, `a` is not constant, all are nonzero, yet
`a * b * c` has no rational root at all, so the right-hand side is `0` while the left-hand
side is `2`.  Likewise, in characteristic `p` the theorem fails (e.g. `a = X ^ p`, `b = 1`,
`c = X ^ p + 1` over `𝔽_p`).

Both defects are repaired by the standard hypotheses under which "number of distinct roots of
`a * b * c`" is the correct reading of "degree of the radical of `a * b * c`": the field is
algebraically closed and of characteristic zero.  The mathematical content (Mason–Stothers) is
unchanged.  A `DecidableEq K` instance is added since `Multiset.toFinset` requires it.
-/

/-- Over an algebraically closed field of characteristic zero, the degree of the radical of a
nonzero polynomial is bounded by its number of distinct roots (in fact they are equal). -/
lemma natDegree_radical_le_card_roots {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    [IsAlgClosed K] {p : K[X]} (hp : p ≠ 0) :
    (radical p).natDegree ≤ p.roots.toFinset.card := by
  -- Step 1: radical p splits over algebraically closed K
  have hsplits : (radical p).Splits := IsAlgClosed.splits _
  -- Step 2: natDegree (radical p) = (radical p).roots.card
  rw [hsplits.natDegree_eq_card_roots]
  -- Step 3: radical p has no repeated roots, so card = toFinset.card
  have hsf : Squarefree (radical p) := squarefree_radical
  have hnodup : (radical p).roots.Nodup := by
    rw [nodup_roots_iff_of_splits (radical_ne_zero (a := p)) hsplits]
    exact PerfectField.separable_iff_squarefree.mpr hsf
  rw [← Multiset.toFinset_card_of_nodup hnodup]
  -- radical p divides p^natDegree, so its roots are roots of p
  apply Finset.card_le_card
  -- Need: (radical p).roots.toFinset ⊆ p.roots.toFinset
  -- It suffices to show every root of radical p is a root of p
  intro x hx
  simp at hx ⊢
  refine ⟨hp, ?_⟩
  -- radical p divides p, so any root of radical p is a root of p
  have hdiv : radical p ∣ p := radical_dvd_self
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hx

/-- **Mason–Stothers** (polynomial abc): for coprime polynomials with `a + b = c`, not all
constant, `max (deg a) (deg b) (deg c)` is less than the number of distinct roots of `a * b * c`.
-/
theorem mason_stothers {K : Type*} [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]
    (a b c : Polynomial K)
    (hab : IsCoprime a b) (hsum : a + b = c) (hnc : ¬ (a.natDegree = 0 ∧ b.natDegree = 0))
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    max (max a.natDegree b.natDegree) c.natDegree <
      (a * b * c).roots.toFinset.card := by
  have hsum' : a + b + (-c) = 0 := by rw [hsum]; ring
  have := Polynomial.abc ha hb (neg_ne_zero.mpr hc) hab hsum'
  rcases this with hrad | hderiv
  · -- Case: radical degree bounds
    -- We need: max (max a.natDegree b.natDegree) c.natDegree < (a * b * c).roots.toFinset.card
    -- From hrad: a.natDegree + 1 ≤ radical(a * b * -c).natDegree, etc.
    -- radical(a * b * -c) = radical(a * b * c)
    have hr_eq : radical (a * b * -c) = radical (a * b * c) := by
      have hassoc : Associated (a * b * -c) (a * b * c) := by
        refine ⟨-1, ?_⟩
        simp [Units.val_neg]
      exact radical_eq_of_associated hassoc
    -- Use the helper lemma
    have hr_le := natDegree_radical_le_card_roots (mul_ne_zero (mul_ne_zero ha hb) hc)
    -- Rewrite using hr_eq
    rw [hr_eq] at hrad
    -- Extract the bounds
    obtain ⟨ha_bound, hb_bound, hc_bound⟩ := hrad
    -- natDegree(-c) = natDegree(c)
    have hc_deg : (-c).natDegree = c.natDegree := Polynomial.natDegree_neg c
    rw [hc_deg] at hc_bound
    -- Combine bounds
    have ha_lt : a.natDegree < (a * b * c).roots.toFinset.card := ha_bound.trans hr_le
    have hb_lt : b.natDegree < (a * b * c).roots.toFinset.card := hb_bound.trans hr_le
    have hc_lt : c.natDegree < (a * b * c).roots.toFinset.card := hc_bound.trans hr_le
    -- Combine into max
    simp [ha_lt, hb_lt, hc_lt]
  · -- Case: all derivatives zero (impossible in char 0 for non-constant)
    obtain ⟨ha', hb', hc'⟩ := hderiv
    -- In char 0, derivative = 0 implies constant
    have ha_const : a.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero ha'
    have hb_const : b.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hb'
    exact absurd ⟨ha_const, hb_const⟩ hnc

end Brockian.MasonStothers

