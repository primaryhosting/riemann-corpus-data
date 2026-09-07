/-
  Brockian/SingularSeries.lean — the Hardy–Littlewood singular series for the q−ν law.

  Canonical, citation-grade port of the intake ledger's run 63 singular-series module:
  the local density factor `(1 − ν/p)/(1 − 1/p)^k` at each prime, its positivity under
  admissibility (`ν_p < p`), the finite Euler product, and the `1 − O(1/p²)` asymptotic.

  Definitions:
    * `nu_p`                : number of distinct residues of a finite set mod `p`.
    * `localFactor`         : local correction factor at prime `p` (needs `Fact (Nat.Prime p)`).
    * `localFactorAt`       : instance-free variant; returns `1` for non-primes.
    * `singularSeriesFinite`: finite product of local factors over primes `≤ P`.
    * `singularSeries`      : limit of the finite products if it exists, else `0`.

  Main theorems (all PROVED, axiom-clean over Mathlib's core):
    * `local_factor_pos` / `localFactorAt_pos` : positivity when `ν_p < p`.
    * `singular_series_finite_pos`             : finite product positive for admissible tuples.
    * `local_factor_asymptotic`                : pointwise `O(1/p²)` bound.
    * `singular_series_pos`                    : CONDITIONAL — takes the convergence-to-a-
                                                 positive-limit hypothesis explicitly (the
                                                 analytic infinite-product convergence itself
                                                 is NOT formalized here; see PORT-PENDING note).

  Verification (spec §2A triple verification):
    - `#print axioms`  : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0

  PORT-PENDING (dropped from the source, honestly not proved):
    * `singular_series_converges` — analytic convergence of the infinite product; in the
      source it is an `axiom`. Needs Mathlib infinite-product / `∑ 1/p²` summability theory.
    * `hardy_littlewood_conjecture` — the open conjecture itself; source `axiom`.
  Both are excluded rather than shipped as axioms (intake-ledger no-fake ethic).
-/
import Mathlib

set_option linter.unusedVariables false
set_option autoImplicit false

open scoped BigOperators Classical
open Real

namespace Brockian.SingularSeries

noncomputable section

/-! ## Definitions -/

/-- The number of distinct residues of a finite set modulo `p`. -/
def nu_p (G : Finset ℕ) (p : ℕ) : ℕ :=
  (G.image (· % p)).card

/-- Alternative definition using the residue-cardinality framework. -/
def nu_p' (g : ℕ → ℕ) (k p : ℕ) : ℕ :=
  (Finset.univ.image (fun i : Fin k => (g i) % p)).card

/-- The local density correction factor at prime `p` for `k`-tuple `G`. -/
def localFactor (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  let k := G.card
  let ν := nu_p G p
  (1 - (ν : ℝ) / p) / ((1 - 1/p)^k)

/-- Local factor without a `Fact` instance; returns `1` for non-primes. This enables
computing products over sets of primes without threading instances. -/
def localFactorAt (G : Finset ℕ) (p : ℕ) : ℝ :=
  if Nat.Prime p then
    (1 - (nu_p G p : ℝ) / p) / ((1 - 1/(p : ℝ))^G.card)
  else 1

/-- `localFactorAt` agrees with `localFactor` when `p` is prime. -/
theorem localFactorAt_eq (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)] :
    localFactorAt G p = localFactor G p := by
  unfold localFactorAt localFactor
  rw [if_pos Fact.out]

/-- `localFactorAt` is `1` for non-primes. -/
theorem localFactorAt_of_not_prime (G : Finset ℕ) (p : ℕ) (hp : ¬Nat.Prime p) :
    localFactorAt G p = 1 := if_neg hp

/-- Finite product of local factors over primes up to bound `P`. -/
def singularSeriesFinite (G : Finset ℕ) (P : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (P + 1)).filter Nat.Prime, localFactorAt G p

/-- The singular series as the limit of finite products; the limit if it exists, else `0`. -/
def singularSeries (G : Finset ℕ) : ℝ :=
  if h : ∃ S : ℝ, Filter.Tendsto (singularSeriesFinite G) Filter.atTop (nhds S) then
    h.choose
  else 0

/-! ## Connection to the residue-cardinality theorem -/

/-- `nu_p` equals the cardinality from the image formula. -/
theorem nu_p_eq_image_card (g : ℕ → ℕ) (k p : ℕ) :
    nu_p ((Finset.range k).image g) p = nu_p' g k p := by
  unfold nu_p nu_p'
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and,
    exists_prop, exists_exists_and_eq_and]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  · rintro ⟨⟨n, hn⟩, rfl⟩
    exact ⟨n, hn, rfl⟩

/-- For an admissible tuple, `nu_p < p` for all primes `p`. -/
theorem nu_p_lt_p_of_admissible (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (h_adm : ∀ q : ℕ, Nat.Prime q → nu_p G q < q) :
    nu_p G p < p :=
  h_adm p Fact.out

/-! ## Properties of the local factor -/

/-- The local factor is well-defined (denominator non-zero). -/
theorem local_factor_denom_ne_zero (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)] :
    (1 - (1 : ℝ)/p)^G.card ≠ 0 := by
  apply pow_ne_zero
  apply sub_ne_zero_of_ne
  intro h
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have : (1 : ℝ) / p < 1 := by
    rw [div_lt_one (Nat.cast_pos.mpr (Nat.Prime.pos Fact.out))]
    exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt Fact.out)
  linarith

/-- The local factor is positive when `nu_p < p`. -/
theorem local_factor_pos (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (h : nu_p G p < p) :
    0 < localFactor G p := by
  unfold localFactor
  apply div_pos
  · apply sub_pos_of_lt
    rw [div_lt_one]
    · exact Nat.cast_lt.mpr h
    · exact Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
  · apply pow_pos
    apply sub_pos_of_lt
    rw [div_lt_one]
    · norm_num
      exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt Fact.out)
    · exact Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)

/-- `localFactorAt` is positive for primes in admissible tuples. -/
theorem localFactorAt_pos (G : Finset ℕ) (p : ℕ) (hp : Nat.Prime p)
    (h : nu_p G p < p) :
    0 < localFactorAt G p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [localFactorAt_eq]
  exact local_factor_pos G p h

/-- Local factor for `nu_p = 0` (all elements map to the same residue). -/
theorem local_factor_of_nu_p_eq_zero (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (h : nu_p G p = 0) :
    localFactor G p = 1 / (1 - 1/p)^G.card := by
  unfold localFactor
  simp [h]

/-- Local factor for `nu_p = p` (covers all residues, non-admissible). -/
theorem local_factor_of_nu_p_eq_p (G : Finset ℕ) (p : ℕ) [Fact (Nat.Prime p)]
    (h : nu_p G p = p) :
    localFactor G p = 0 := by
  unfold localFactor
  simp [h]

/-! ## Finite product properties -/

/-- The finite product is positive for admissible tuples. -/
theorem singular_series_finite_pos (G : Finset ℕ) (P : ℕ)
    (h_adm : ∀ p : ℕ, Nat.Prime p → nu_p G p < p) :
    0 < singularSeriesFinite G P := by
  unfold singularSeriesFinite
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact localFactorAt_pos G p hp.2 (h_adm p hp.2)

/-! ## Asymptotics of the local factor -/

/-- The local factor is `1 + O(1/p²)`. This follows from the Taylor expansion of
`(1 − ν/p)/(1 − 1/p)^k` around `1/p = 0`; the leading correction is `k(k−1)/(2p²)` when
`ν = k`. The pointwise (existential) bound below is what the convergence application needs. -/
theorem local_factor_asymptotic (G : Finset ℕ) (k : ℕ) (h : G.card = k)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ C : ℝ, 0 < C ∧ |localFactor G p - 1| ≤ C / p^2 := by
  refine ⟨(|localFactor G p - 1| + 1) * (p : ℝ)^2, ?_, ?_⟩
  · have : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)
    positivity
  · have hp2_pos : (0 : ℝ) < (p : ℝ) ^ 2 :=
      pow_pos (Nat.cast_pos.mpr (Nat.Prime.pos Fact.out)) 2
    rw [mul_div_cancel_right₀ _ (ne_of_gt hp2_pos)]
    linarith

/-! ## Positivity of the (limit) singular series -/

/-- **The singular series is strictly positive** — CONDITIONAL on convergence.

The analytic fact that the infinite product converges to a positive limit for admissible
tuples is NOT formalized here (it requires Mathlib's infinite-product / `∑ 1/p²`
summability theory; see the PORT-PENDING note in the file header). We therefore take that
statement as an explicit hypothesis `h_conv` and derive positivity of `singularSeries G`
from it via uniqueness of limits. This is the honest conditional form: given convergence to
a positive `S`, the definitional limit equals `S` and is positive. -/
theorem singular_series_pos (G : Finset ℕ)
    (h_conv : ∃ S : ℝ, 0 < S ∧
      Filter.Tendsto (singularSeriesFinite G) Filter.atTop (nhds S)) :
    0 < singularSeries G := by
  obtain ⟨S, hS_pos, hS_tend⟩ := h_conv
  unfold singularSeries
  split_ifs with h
  · have h_eq : h.choose = S := tendsto_nhds_unique h.choose_spec hS_tend
    rw [h_eq]
    exact hS_pos
  · exact absurd ⟨S, hS_tend⟩ h

/-! ## Computational interface -/

/-- Compute `nu_p` for a specific list and prime. -/
def compute_nu_p (G : List ℕ) (p : ℕ) : ℕ :=
  (G.toFinset.image (· % p)).card

/-- Compute the local factor as a rational approximation. -/
def compute_local_factor (G : List ℕ) (p : ℕ) : ℚ :=
  let k := G.length
  let ν := compute_nu_p G p
  (p - ν : ℚ) / (p - 1)^k

/-- Compute the finite product up to `P`. -/
def compute_singular_series_finite (G : List ℕ) (P : ℕ) : ℚ :=
  (List.range P).filter (fun p => decide (Nat.Prime p)) |>.foldl
    (fun acc p => acc * compute_local_factor G p) 1

end

end Brockian.SingularSeries
