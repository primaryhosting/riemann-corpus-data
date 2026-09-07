/-
  Brockian/SingularSeriesConvergence.lean — analytic convergence of the singular series.

  Discharges the PORT-PENDING `singular_series_converges` that `Brockian.SingularSeries`
  formerly assumed (and that `singular_series_pos` still takes as the hypothesis `h_conv`).
  This is the honest, unconditional analytic input: for an admissible tuple `G` the infinite
  Euler product `∏_p localFactor p` converges to a strictly positive limit.

  Roadmap item #17 (PORT-QUEUE): the dropped axiom `singular_series_converges` is here
  replaced by a genuine Lean 4 / Mathlib proof — NOT reintroduced as an axiom.

  Strategy (no new axioms, no `sorry`):
    * `err_bound`             : `|(1-x)^k - (1 - k·x)| ≤ k²·x²` for `0 ≤ x ≤ 1`
                               (elementary induction, the Taylor tail `1 - k·x + O(x²)`).
    * `nu_p_eq_card_of_lt`    : for `p` exceeding every element of `G`, `nu_p G p = G.card`
                               (the residue map is injective on `G`), so only finitely many
                               primes deviate — the tail has `ν = k`.
    * `localFactor_sub_one_bound` : the uniform tail bound
                               `|localFactor G p − 1| ≤ 2^k · k² / p²` when `ν = k`.
    * `summable_localFactorAt_sub_one` : hence `∑_p |localFactor p − 1|` converges
                               (comparison with the convergent `∑ 1/p²`, shifting past the
                               finitely many small primes via `summable_nat_add_iff`).
    * `singularSeriesFinite_tendsto_pos` : from summable logs (`Real.multipliable_of_summable_log`)
                               the product is multipliable, its partial products
                               (`= singularSeriesFinite`) converge, and the limit
                               `= rexp (∑ log …) > 0` (`Real.rexp_tsum_eq_tprod`).
    * `singular_series_pos'`  : UNCONDITIONAL positivity of `singularSeries G`, discharging
                               the `h_conv` hypothesis of `singular_series_pos`.

  Verification (AXLE, spec §2A):
    - `#print axioms` : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib
import Brockian.SingularSeries

set_option linter.unusedVariables false
set_option autoImplicit false

open scoped BigOperators
open Brockian.SingularSeries

namespace Brockian.SingularSeries.Convergence

/-! ## Elementary Taylor-tail bound -/

/-- `(1-x)^k = 1 - k·x + O(x²)`: the quadratic remainder is bounded by `k²·x²` on `[0,1]`.
Proved by induction using the exact recurrence `E_{k+1} = (1-x)·E_k + k·x²`. -/
theorem err_bound (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(1 - x) ^ k - (1 - (k : ℝ) * x)| ≤ (k : ℝ) ^ 2 * x ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1x : (0 : ℝ) ≤ 1 - x := by linarith
    have h1x' : (1 : ℝ) - x ≤ 1 := by linarith
    have hid : (1 - x) ^ (k + 1) - (1 - ((k : ℝ) + 1) * x)
        = (1 - x) * ((1 - x) ^ k - (1 - (k : ℝ) * x)) + (k : ℝ) * x ^ 2 := by
      rw [pow_succ]; ring
    have hcast : (1 - (((k + 1 : ℕ)) : ℝ) * x) = (1 - ((k : ℝ) + 1) * x) := by
      push_cast; ring
    rw [hcast, hid]
    push_cast
    calc |(1 - x) * ((1 - x) ^ k - (1 - (k : ℝ) * x)) + (k : ℝ) * x ^ 2|
        ≤ |(1 - x) * ((1 - x) ^ k - (1 - (k : ℝ) * x))| + |(k : ℝ) * x ^ 2| := abs_add_le _ _
      _ = (1 - x) * |(1 - x) ^ k - (1 - (k : ℝ) * x)| + (k : ℝ) * x ^ 2 := by
          rw [abs_mul, abs_of_nonneg h1x,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * x ^ 2)]
      _ ≤ 1 * ((k : ℝ) ^ 2 * x ^ 2) + (k : ℝ) * x ^ 2 := by
          have hstep2 : (1 - x) * |(1 - x) ^ k - (1 - (k : ℝ) * x)| ≤ 1 * ((k : ℝ) ^ 2 * x ^ 2) :=
            calc (1 - x) * |(1 - x) ^ k - (1 - (k : ℝ) * x)|
                ≤ 1 * |(1 - x) ^ k - (1 - (k : ℝ) * x)| :=
                  mul_le_mul_of_nonneg_right h1x' (abs_nonneg _)
              _ ≤ 1 * ((k : ℝ) ^ 2 * x ^ 2) := mul_le_mul_of_nonneg_left ih (by norm_num)
          linarith
      _ = ((k : ℝ) ^ 2 + (k : ℝ)) * x ^ 2 := by ring
      _ ≤ ((k : ℝ) + 1) ^ 2 * x ^ 2 := by
          have hkk : (k : ℝ) ^ 2 + (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
            nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
          exact mul_le_mul_of_nonneg_right hkk (by positivity)

/-! ## The residue count saturates for large primes -/

/-- If `p` exceeds every element of `G`, the residues `a % p` are all distinct, so
`nu_p G p = G.card`. This shows only finitely many primes contribute a deviation of
order `1/p` — the analytic tail all has `ν = k`. -/
theorem nu_p_eq_card_of_lt (G : Finset ℕ) (p : ℕ) (h : ∀ a ∈ G, a < p) :
    nu_p G p = G.card := by
  unfold nu_p
  have hInj : Set.InjOn (· % p) ↑G := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [Nat.mod_eq_of_lt (h a ha), Nat.mod_eq_of_lt (h b hb)] at hab
    exact hab
  rw [Finset.card_image_of_injOn hInj]

/-! ## Uniform `O(1/p²)` bound on the tail factors -/

/-- The core uniform bound: when `p` exceeds every element of `G` (so `ν = k`) and `p ≥ 2`,
`|localFactor G p − 1| ≤ 2^k · k² / p²`, a summable comparison term. -/
theorem localFactor_sub_one_bound (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (hp2 : 2 ≤ p) (hlt : ∀ a ∈ G, a < p) :
    |localFactor G p - 1| ≤ (2 : ℝ) ^ G.card * (G.card : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
  have hpR2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hxhalf : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have hx1 : (1 : ℝ) / (p : ℝ) ≤ 1 := by linarith
  have hhalf_le : (1 : ℝ) / 2 ≤ 1 - 1 / (p : ℝ) := by linarith
  have h1xpos : (0 : ℝ) < 1 - 1 / (p : ℝ) := by linarith
  have hdenpos : (0 : ℝ) < (1 - 1 / (p : ℝ)) ^ G.card := pow_pos h1xpos _
  have hDne : (1 - 1 / (p : ℝ)) ^ G.card ≠ 0 := ne_of_gt hdenpos
  have hden_lb : (1 / 2 : ℝ) ^ G.card ≤ (1 - 1 / (p : ℝ)) ^ G.card :=
    pow_le_pow_left₀ (by norm_num) hhalf_le G.card
  have half_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ G.card := by positivity
  have hnu : nu_p G p = G.card := nu_p_eq_card_of_lt G p hlt
  have hLF0 : localFactor G p
      = (1 - (nu_p G p : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ G.card := rfl
  have hLF : localFactor G p
      = (1 - (G.card : ℝ) * (1 / (p : ℝ))) / (1 - 1 / (p : ℝ)) ^ G.card := by
    rw [hLF0, hnu, mul_one_div]
  have hsub : ((1 - (G.card : ℝ) * (1 / (p : ℝ))) - (1 - 1 / (p : ℝ)) ^ G.card)
        / (1 - 1 / (p : ℝ)) ^ G.card
      = localFactor G p - 1 := by
    rw [hLF, sub_div, div_self hDne]
  have habs : |localFactor G p - 1|
      = |(1 - (G.card : ℝ) * (1 / (p : ℝ))) - (1 - 1 / (p : ℝ)) ^ G.card|
        / (1 - 1 / (p : ℝ)) ^ G.card := by
    rw [← hsub, abs_div, abs_of_pos hdenpos]
  have hnum : |(1 - 1 / (p : ℝ)) ^ G.card - (1 - (G.card : ℝ) * (1 / (p : ℝ)))|
      ≤ (G.card : ℝ) ^ 2 * (1 / (p : ℝ)) ^ 2 :=
    err_bound G.card (1 / (p : ℝ)) hx0 hx1
  rw [habs, abs_sub_comm]
  calc |(1 - 1 / (p : ℝ)) ^ G.card - (1 - (G.card : ℝ) * (1 / (p : ℝ)))|
          / (1 - 1 / (p : ℝ)) ^ G.card
      ≤ ((G.card : ℝ) ^ 2 * (1 / (p : ℝ)) ^ 2) / (1 / 2 : ℝ) ^ G.card := by
        rw [div_le_div_iff₀ hdenpos half_pos]
        calc |(1 - 1 / (p : ℝ)) ^ G.card - (1 - (G.card : ℝ) * (1 / (p : ℝ)))|
                * (1 / 2 : ℝ) ^ G.card
            ≤ ((G.card : ℝ) ^ 2 * (1 / (p : ℝ)) ^ 2) * (1 / 2 : ℝ) ^ G.card :=
              mul_le_mul_of_nonneg_right hnum (le_of_lt half_pos)
          _ ≤ ((G.card : ℝ) ^ 2 * (1 / (p : ℝ)) ^ 2) * (1 - 1 / (p : ℝ)) ^ G.card :=
              mul_le_mul_of_nonneg_left hden_lb (by positivity)
    _ = (2 : ℝ) ^ G.card * (G.card : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
        have h2kne : (2 : ℝ) ^ G.card ≠ 0 := by positivity
        rw [show (1 / (p : ℝ)) ^ 2 = 1 / (p : ℝ) ^ 2 from by rw [div_pow, one_pow],
            show (1 / 2 : ℝ) ^ G.card = 1 / (2 : ℝ) ^ G.card from by rw [div_pow, one_pow]]
        field_simp

/-! ## Summability of the deviations -/

/-- `∑_p |localFactor p − 1|` converges: the finitely many small primes are shifted past
with `summable_nat_add_iff`, and the tail is dominated by the convergent `∑ 2^k·k²/p²`. -/
theorem summable_localFactorAt_sub_one (G : Finset ℕ)
    (h_adm : ∀ p : ℕ, Nat.Prime p → nu_p G p < p) :
    Summable (fun p => |localFactorAt G p - 1|) := by
  set N := G.sup id + 1 with hN
  rw [← summable_nat_add_iff N]
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((n + N : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) N).mpr hbase
  have hg : Summable
      (fun n : ℕ => (2 : ℝ) ^ G.card * (G.card : ℝ) ^ 2 / ((n + N : ℕ) : ℝ) ^ 2) := by
    have hc := hshift.mul_left ((2 : ℝ) ^ G.card * (G.card : ℝ) ^ 2)
    exact hc.congr (fun n => (mul_one_div _ _))
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hg
  by_cases hprime : Nat.Prime (n + N)
  · haveI : Fact (Nat.Prime (n + N)) := ⟨hprime⟩
    have hp2 : 2 ≤ n + N := hprime.two_le
    have hlt : ∀ a ∈ G, a < n + N := by
      intro a ha
      have hle : a ≤ G.sup id := Finset.le_sup (f := id) ha
      omega
    rw [localFactorAt_eq]
    exact localFactor_sub_one_bound G (n + N) hp2 hlt
  · rw [localFactorAt_of_not_prime G (n + N) hprime, sub_self, abs_zero]
    positivity

/-! ## Convergence to a positive limit -/

/-- **The singular series converges to a strictly positive limit.**  For an admissible tuple
`G` (`ν_p < p` for all primes), the partial Euler products `singularSeriesFinite G P` tend to
a positive `S`.  This is exactly the `h_conv` shape assumed by `singular_series_pos`. -/
theorem singularSeriesFinite_tendsto_pos (G : Finset ℕ)
    (h_adm : ∀ p : ℕ, Nat.Prime p → nu_p G p < p) :
    ∃ S : ℝ, 0 < S ∧ Filter.Tendsto (singularSeriesFinite G) Filter.atTop (nhds S) := by
  have hpos : ∀ p, 0 < localFactorAt G p := by
    intro p
    by_cases hp : Nat.Prime p
    · exact localFactorAt_pos G p hp (h_adm p hp)
    · rw [localFactorAt_of_not_prime G p hp]; norm_num
  have hsum_abs := summable_localFactorAt_sub_one G h_adm
  have hsum : Summable (fun p => localFactorAt G p - 1) := hsum_abs.of_abs
  have hlog : Summable (fun p => Real.log (localFactorAt G p)) := by
    have h1 := Real.summable_log_one_add_of_summable hsum
    refine h1.congr (fun p => ?_)
    rw [show (1 : ℝ) + (localFactorAt G p - 1) = localFactorAt G p from by ring]
  have hmul : Multipliable (localFactorAt G) := Real.multipliable_of_summable_log hpos hlog
  refine ⟨∏' p, localFactorAt G p, ?_, ?_⟩
  · rw [← Real.rexp_tsum_eq_tprod hpos hlog]
    exact Real.exp_pos _
  · have htend : Filter.Tendsto (fun n => ∏ i ∈ Finset.range n, localFactorAt G i)
        Filter.atTop (nhds (∏' p, localFactorAt G p)) := hmul.tendsto_prod_tprod_nat
    have htend1 : Filter.Tendsto (fun P => ∏ i ∈ Finset.range (P + 1), localFactorAt G i)
        Filter.atTop (nhds (∏' p, localFactorAt G p)) :=
      htend.comp (Filter.tendsto_add_atTop_nat 1)
    refine htend1.congr (fun P => ?_)
    unfold singularSeriesFinite
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) (fun x hx hxns => ?_)
    have hxnp : ¬ Nat.Prime x := fun hxp => hxns (Finset.mem_filter.mpr ⟨hx, hxp⟩)
    exact localFactorAt_of_not_prime G x hxnp

/-- **Unconditional positivity of the singular series.**  Discharges the convergence
hypothesis `h_conv` of `Brockian.SingularSeries.singular_series_pos`, so admissibility alone
now proves `0 < singularSeries G`. -/
theorem singular_series_pos' (G : Finset ℕ)
    (h_adm : ∀ p : ℕ, Nat.Prime p → nu_p G p < p) :
    0 < singularSeries G :=
  singular_series_pos G (singularSeriesFinite_tendsto_pos G h_adm)

end Brockian.SingularSeries.Convergence
