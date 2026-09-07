import Mathlib

/-!
# A finite Selberg/Ruelle-style trace formula

For a permutation `σ : Equiv.Perm X` of a finite type `X`, its permutation ("transfer")
matrix `P = σ.toPEquiv.toMatrix : Matrix X X ℤ` satisfies the **finite trace formula**

    Tr(P ^ n)  =  #{ x : σ^n x = x }  =  ∑_{ℓ ∣ n} #{ x : minimalPeriod σ x = ℓ }.

Reading the geometric side: `#{ x : minimalPeriod σ x = ℓ } = ℓ · (number of length-ℓ orbits)`,
so the right-hand side is the sum of the **lengths of the closed orbits whose length divides `n`**.
Thus the `n`-th trace on the spectral side equals a sum over closed orbits on the geometric
side — the finite analogue of the Selberg/Ruelle trace formula (`ζ`-side ↔ orbit-side).
-/

namespace Brockian.PhaseDepthTraceFormula

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The **transfer operator** of `σ`: its permutation matrix over `ℤ`. -/
def permMatrix (σ : Equiv.Perm X) : Matrix X X ℤ := σ.toPEquiv.toMatrix

/-- Powers of the permutation matrix are the permutation matrices of the powers of `σ`
(the map `σ ↦ σ.toPEquiv.toMatrix` sends composition to matrix multiplication). -/
lemma permMatrix_pow (σ : Equiv.Perm X) (n : ℕ) :
    (permMatrix σ) ^ n = ((σ ^ n).toPEquiv.toMatrix) := by
  simp only [permMatrix]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Equiv.Perm.one_def, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  | succ k ih =>
    rw [pow_succ, ih, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
        ← Equiv.Perm.mul_def, ← pow_succ']

/-- **Target 1 — spectral side counts fixed points.**
`Tr(P^n)` is literally the number of points fixed by `σ^n`. -/
theorem trace_pow_eq_periodic_card (σ : Equiv.Perm X) (n : ℕ) :
    Matrix.trace ((permMatrix σ) ^ n)
      = ((Finset.univ.filter (fun x => (σ ^ n) x = x)).card : ℤ) := by
  rw [permMatrix_pow]
  delta Matrix.trace
  simp only [Matrix.diag_apply]
  have hsum : (∑ i : X, ((σ ^ n).toPEquiv.toMatrix) i i)
        = ∑ i : X, (if (σ ^ n) i = i then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff]
  rw [hsum, Finset.sum_boole]

/-- **Target 2 — the orbit decomposition (THE trace formula, geometric side).**
For `n ≥ 1`, the number of `σ^n`-fixed points splits, according to the length `ℓ` of the
orbit each point lies on, as a sum over the divisors `ℓ ∣ n`:

    #{ x : σ^n x = x }  =  ∑_{ℓ ∣ n} #{ x : minimalPeriod σ x = ℓ }.

A point is fixed by `σ^n` iff its minimal period divides `n`; grouping such points by their
minimal period (which then ranges over the divisors of `n`) gives the decomposition.  Since a
length-`ℓ` orbit contributes exactly `ℓ` points all of minimal period `ℓ`, the `ℓ`-th summand
equals `ℓ ·(number of length-ℓ orbits)`, so the right-hand side is the sum of the lengths of
the closed orbits whose length divides `n`. -/
theorem periodic_card_eq_orbit_sum (σ : Equiv.Perm X) {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter (fun x => (σ ^ n) x = x)).card
      = ∑ ℓ ∈ n.divisors,
          (Finset.univ.filter (fun x => Function.minimalPeriod (⇑σ) x = ℓ)).card := by
  -- A point is `σ^n`-fixed iff its minimal period divides `n`.
  have key : ∀ x : X, ((σ ^ n) x = x) ↔ Function.minimalPeriod (⇑σ) x ∣ n := by
    intro x
    have hcoe : (σ ^ n) x = (⇑σ)^[n] x := by rw [Equiv.Perm.coe_pow]
    rw [hcoe]
    exact Function.isPeriodicPt_iff_minimalPeriod_dvd
  have hfilter : (Finset.univ.filter (fun x => (σ ^ n) x = x))
      = Finset.univ.filter (fun x => Function.minimalPeriod (⇑σ) x ∣ n) := by
    apply Finset.filter_congr
    intro x _
    exact key x
  rw [hfilter]
  -- The value `minimalPeriod σ x` of a point in the filtered set lands in `n.divisors`.
  have H : ∀ x ∈ Finset.univ.filter (fun x => Function.minimalPeriod (⇑σ) x ∣ n),
      Function.minimalPeriod (⇑σ) x ∈ n.divisors := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Nat.mem_divisors]
    exact ⟨hx.2, Nat.one_le_iff_ne_zero.mp hn⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  -- Reindex each fiber: filtering the `∣n` set by `= ℓ` is filtering all of `X` by `= ℓ`.
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    exact ⟨by rw [h]; exact (Nat.mem_divisors.mp hℓ).1, h⟩

/-- **Target 3 — the finite trace formula.**
Combining Targets 1 and 2: for `n ≥ 1`, the `n`-th trace of the transfer operator (spectral
side) equals the sum over closed orbits of length dividing `n` (geometric side):

    Tr(P^n)  =  ∑_{ℓ ∣ n} #{ x : minimalPeriod σ x = ℓ }. -/
theorem trace_pow_eq_orbit_sum (σ : Equiv.Perm X) {n : ℕ} (hn : 1 ≤ n) :
    Matrix.trace ((permMatrix σ) ^ n)
      = ((∑ ℓ ∈ n.divisors,
            (Finset.univ.filter (fun x => Function.minimalPeriod (⇑σ) x = ℓ)).card : ℕ) : ℤ) := by
  rw [trace_pow_eq_periodic_card, periodic_card_eq_orbit_sum σ hn]

end Brockian.PhaseDepthTraceFormula
