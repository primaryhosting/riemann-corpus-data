/-
  Brockian/GoldbachLemmas.lean — unconditional lemmas for the Goldbach singular series.

  These are small, honest, fully-proved facts feeding the ANALYTIC side of the binary
  Goldbach problem (Hardy–Littlewood). NONE of this proves Goldbach; it establishes the
  algebraic and combinatorial building blocks of the singular series 𝔖(N).

  For an even N, Hardy–Littlewood predicts
      r(N) ~ 𝔖(N) · N / (log N)²,     𝔖(N) = 2·C₂ · ∏_{p | N, p>2} (p-1)/(p-2),
  where C₂ = ∏_{p≥3} (1 - 1/(p-1)²) is the twin-prime constant. The odd-prime local
  densities are:
      p ∤ N :  1 - 1/(p-1)²  =  p(p-2)/(p-1)²          (generic factor)
      p | N :  p/(p-1)                                  (divisor factor)
  and the ratio (divisor)/(generic) = (p-1)/(p-2) is exactly the product-form factor.

  Contents (all PROVED, unconditional, axiom-clean over Mathlib):

  Real / algebraic side:
    * gFactor p = (p-1)/(p-2)           — the singular product factor at an odd prime.
      - gFactor_pos, one_lt_gFactor, gFactor_eq_one_add : positivity / >1 / exact form.
      - gFactor_pos_prime, one_lt_gFactor_prime         : prime corollaries (odd p>2).
    * tFactor p = 1 - 1/(p-1)²          — the generic (p∤N) local factor.
      - tFactor_eq, tFactor_pos, tFactor_lt_one.
    * factor_ratio : (p/(p-1)) / tFactor p = gFactor p — the key connecting identity.
    * gProduct S = ∏_{p∈S} gFactor p    — the finite product form.
      - gProduct_pos, one_le_gProduct   : positive, bounded below by 1 (a fixed constant,
                                          quantified OUTSIDE the set — no self-reference).

  Combinatorial side (exact representation counts mod p):
    * gResidues p n = { a : ZMod p | a ≠ 0 ∧ n - a ≠ 0 } — the first coordinates of
      representations n = a + b with a,b ≠ 0 mod p.
      - gResidues_card_ne_zero : n ≠ 0 → card = p - 2   (the p∤N count).
      - gResidues_card_zero    : n = 0 → card = p - 1   (the p|N count).
    * localDensity_ne / localDensity_zero : the counts p-2, p-1 recover tFactor and the
      divisor factor p/(p-1) after normalizing by ((p-1)/p)².

  Verification: AXLE `check` @ lean-4.32.0, #print axioms ⊆ {propext, Classical.choice,
  Quot.sound}. No sorry/admit/axiom/native_decide/maxHeartbeats.
-/
import Mathlib

set_option linter.unusedVariables false
set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Brockian.GoldbachLemmas

/-! ## Elementary arithmetic helper -/

/-- A prime other than `2` is at least `3`. -/
theorem three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  rcases (hp.two_le).lt_or_eq with h | h
  · omega
  · exact absurd h.symm h2

/-! ## The singular-series product factor `gFactor p = (p-1)/(p-2)` -/

/-- The Goldbach singular-series factor at an odd prime `p`. -/
noncomputable def gFactor (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- Real bound: `p ≥ 3` gives `(p:ℝ) - 2 ≥ 1 > 0`. -/
private theorem sub_two_pos {p : ℕ} (hp : 3 ≤ p) : (0 : ℝ) < (p : ℝ) - 2 := by
  have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

/-- Real bound: `p ≥ 3` gives `(p:ℝ) - 1 ≥ 2 > 0`. -/
private theorem sub_one_pos {p : ℕ} (hp : 3 ≤ p) : (0 : ℝ) < (p : ℝ) - 1 := by
  have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

/-- The singular factor is strictly positive for `p ≥ 3`. -/
theorem gFactor_pos {p : ℕ} (hp : 3 ≤ p) : 0 < gFactor p := by
  unfold gFactor
  exact div_pos (by have := sub_one_pos hp; linarith) (sub_two_pos hp)

/-- The singular factor exceeds `1` for `p ≥ 3` (since `p-1 > p-2 > 0`). -/
theorem one_lt_gFactor {p : ℕ} (hp : 3 ≤ p) : 1 < gFactor p := by
  unfold gFactor
  rw [one_lt_div (sub_two_pos hp)]
  linarith

/-- Exact form: `(p-1)/(p-2) = 1 + 1/(p-2)`. -/
theorem gFactor_eq_one_add {p : ℕ} (hp : 3 ≤ p) :
    gFactor p = 1 + 1 / ((p : ℝ) - 2) := by
  unfold gFactor
  have h := ne_of_gt (sub_two_pos hp)
  field_simp
  try ring

/-- Prime corollary: the factor is positive at any odd prime `p > 2`. -/
theorem gFactor_pos_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 0 < gFactor p :=
  gFactor_pos (three_le_of_prime_ne_two hp h2)

/-- Prime corollary: the factor exceeds `1` at any odd prime `p > 2`. -/
theorem one_lt_gFactor_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 1 < gFactor p :=
  one_lt_gFactor (three_le_of_prime_ne_two hp h2)

/-! ## The generic (`p ∤ N`) local factor `tFactor p = 1 - 1/(p-1)²` -/

/-- The generic local density factor at an odd prime `p`. -/
noncomputable def tFactor (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- Closed form: `1 - 1/(p-1)² = p(p-2)/(p-1)²`. -/
theorem tFactor_eq {p : ℕ} (hp : 3 ≤ p) :
    tFactor p = (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  unfold tFactor
  have h := ne_of_gt (sub_one_pos hp)
  field_simp
  ring

/-- The generic factor is strictly positive for `p ≥ 3`. -/
theorem tFactor_pos {p : ℕ} (hp : 3 ≤ p) : 0 < tFactor p := by
  rw [tFactor_eq hp]
  apply div_pos
  · exact mul_pos (by have := sub_one_pos hp; linarith) (sub_two_pos hp)
  · exact pow_pos (sub_one_pos hp) 2

/-- The generic factor is strictly below `1` for `p ≥ 2` (`1/(p-1)² > 0`). -/
theorem tFactor_lt_one {p : ℕ} (hp : 2 ≤ p) : tFactor p < 1 := by
  unfold tFactor
  have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpos : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by positivity
  have : (0 : ℝ) < 1 / ((p : ℝ) - 1) ^ 2 := by positivity
  linarith

/-! ## The key connecting identity -/

/-- The divisor factor `p/(p-1)` divided by the generic factor `tFactor p` equals the
singular product factor `(p-1)/(p-2)`. This is what turns the Euler product
`∏ (p∤N-factor)` with correction into `2·C₂·∏_{p|N} (p-1)/(p-2)`. -/
theorem factor_ratio {p : ℕ} (hp : 3 ≤ p) :
    ((p : ℝ) / ((p : ℝ) - 1)) / tFactor p = gFactor p := by
  rw [tFactor_eq hp]
  unfold gFactor
  have h1 := ne_of_gt (sub_one_pos hp)
  have h2 := ne_of_gt (sub_two_pos hp)
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    positivity
  field_simp
  try ring

/-! ## The finite product form -/

/-- The finite singular product over a set of odd primes. -/
noncomputable def gProduct (S : Finset ℕ) : ℝ := ∏ p ∈ S, gFactor p

/-- The product is strictly positive when every element is `≥ 3`. -/
theorem gProduct_pos {S : Finset ℕ} (h : ∀ p ∈ S, 3 ≤ p) : 0 < gProduct S := by
  unfold gProduct
  exact Finset.prod_pos (fun p hp => gFactor_pos (h p hp))

/-- The product is bounded below by the fixed constant `1` (each factor `≥ 1`), a genuine
lower bound with the constant quantified OUTSIDE the set. -/
theorem one_le_gProduct {S : Finset ℕ} (h : ∀ p ∈ S, 3 ≤ p) : 1 ≤ gProduct S := by
  unfold gProduct
  calc (1 : ℝ) = ∏ p ∈ S, (1 : ℝ) := (Finset.prod_const_one).symm
    _ ≤ ∏ p ∈ S, gFactor p :=
        Finset.prod_le_prod (fun p _ => zero_le_one)
          (fun p hp => le_of_lt (one_lt_gFactor (h p hp)))

/-- Monotone lower bound: `gProduct` over `S` is at least `gProduct` over any subset,
since the extra factors are all `≥ 1`. -/
theorem gProduct_le_of_subset {S T : Finset ℕ} (hST : S ⊆ T)
    (h : ∀ p ∈ T, 3 ≤ p) : gProduct S ≤ gProduct T := by
  have hSpos : 0 < gProduct S := gProduct_pos (fun p hp => h p (hST hp))
  have hge1 : (1 : ℝ) ≤ ∏ p ∈ T \ S, gFactor p := by
    calc (1 : ℝ) = ∏ p ∈ T \ S, (1 : ℝ) := (Finset.prod_const_one).symm
      _ ≤ ∏ p ∈ T \ S, gFactor p :=
          Finset.prod_le_prod (fun p _ => zero_le_one)
            (fun p hp => le_of_lt (one_lt_gFactor (h p (Finset.mem_sdiff.mp hp).1)))
  have hsplit : (∏ p ∈ T \ S, gFactor p) * gProduct S = gProduct T := by
    unfold gProduct
    rw [Finset.prod_sdiff hST]
  calc gProduct S = 1 * gProduct S := (one_mul _).symm
    _ ≤ (∏ p ∈ T \ S, gFactor p) * gProduct S :=
        mul_le_mul_of_nonneg_right hge1 (le_of_lt hSpos)
    _ = gProduct T := hsplit

/-! ## Exact representation counts mod `p` -/

/-- First coordinates `a` of representations `n = a + b` mod `p` with `a ≠ 0`, `b ≠ 0`
(here `b = n - a`). Its cardinality is the exact local representation count. -/
def gResidues (p : ℕ) [NeZero p] (n : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun a => a ≠ 0 ∧ n - a ≠ 0)

/-- For `n ≠ 0` the count is `p - 2`: exactly the `a ∉ {0, n}` residues. This is the
`p ∤ N` local count. -/
theorem gResidues_card_ne_zero {p : ℕ} [NeZero p] {n : ZMod p} (hn : n ≠ 0) :
    (gResidues p n).card = p - 2 := by
  have hset : gResidues p n = Finset.univ \ ({0, n} : Finset (ZMod p)) := by
    unfold gResidues
    rw [Finset.sdiff_eq_filter]
    apply Finset.filter_congr
    intro a _
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, sub_ne_zero]
    constructor
    · rintro ⟨ha0, han⟩
      exact ⟨ha0, fun h => han h.symm⟩
    · rintro ⟨ha0, han⟩
      exact ⟨ha0, fun h => han h.symm⟩
  rw [hset, Finset.card_sdiff, Finset.inter_univ, Finset.card_pair (Ne.symm hn),
    Finset.card_univ, ZMod.card]

/-- For `n = 0` the count is `p - 1`: exactly the nonzero residues (`a` with `a ≠ 0` and
`-a ≠ 0`). This is the `p | N` local count. -/
theorem gResidues_card_zero {p : ℕ} [NeZero p] :
    (gResidues p 0).card = p - 1 := by
  have hset : gResidues p 0 = Finset.univ \ ({0} : Finset (ZMod p)) := by
    unfold gResidues
    rw [Finset.sdiff_eq_filter]
    apply Finset.filter_congr
    intro a _
    simp only [Finset.mem_singleton, zero_sub, neg_ne_zero]
    tauto
  rw [hset, Finset.card_sdiff, Finset.inter_univ, Finset.card_singleton,
    Finset.card_univ, ZMod.card]

/-! ## From counts to local factors -/

/-- Normalizing the `p ∤ N` count `p-2` by `p` and dividing by the density `((p-1)/p)²`
of "both coordinates nonzero" recovers exactly the generic factor `tFactor p`. -/
theorem localDensity_ne {p : ℕ} (hp : 3 ≤ p) :
    (((p : ℝ) - 2) / p) / (((p : ℝ) - 1) / p) ^ 2 = tFactor p := by
  rw [tFactor_eq hp]
  have h1 := ne_of_gt (sub_one_pos hp)
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    positivity
  field_simp
  try ring

/-- Normalizing the `p | N` count `p-1` by `p` and dividing by `((p-1)/p)²` recovers the
divisor factor `p/(p-1)`. -/
theorem localDensity_zero {p : ℕ} (hp : 3 ≤ p) :
    (((p : ℝ) - 1) / p) / (((p : ℝ) - 1) / p) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) := by
  have h1 := ne_of_gt (sub_one_pos hp)
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    positivity
  field_simp
  try ring

end Brockian.GoldbachLemmas
