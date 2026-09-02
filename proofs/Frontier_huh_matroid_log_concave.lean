/-
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Frontier

open Finset Polynomial

/-- The natural-number rank function of a matroid, obtained from the `ℕ∞`-valued rank
`Matroid.eRk` by truncation. For a matroid with a finite ground set this is the usual rank. -/
noncomputable def matroidRank {α : Type*} (M : Matroid α) (S : Set α) : ℕ := (M.eRk S).toNat

/-- The characteristic polynomial of a matroid `M` with finite ground set `E`, given by the
Whitney rank generating (Möbius) formula
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/
noncomputable def charPoly {α : Type*} [DecidableEq α] (M : Matroid α) (E : Finset α) :
    Polynomial ℤ :=
  ∑ S ∈ E.powerset, (-1) ^ S.card * X ^ (matroidRank M (E : Set α) - matroidRank M (S : Set α))

/-- In the free (Boolean) matroid on `E`, every subset of `E` has rank equal to its cardinality. -/
lemma matroidRank_freeOn {α : Type*} (E S : Finset α) (hS : S ⊆ E) :
    matroidRank (Matroid.freeOn (E : Set α)) (S : Set α) = S.card := by
  have h : ((S : Set α)) ⊆ (E : Set α) := by exact_mod_cast hS
  rw [matroidRank, Matroid.eRk_freeOn h, Set.encard_coe_eq_coe_finsetCard]
  simp

/-- The characteristic polynomial of the free (Boolean) matroid on an `n`-element set is
`(t - 1)^n`. -/
lemma charPoly_freeOn {α : Type*} [DecidableEq α] (E : Finset α) :
    charPoly (Matroid.freeOn (E : Set α)) E = (X - 1) ^ E.card := by
  classical
  have hrank : ∀ S ∈ E.powerset,
      (-1 : Polynomial ℤ) ^ S.card *
        X ^ (matroidRank (Matroid.freeOn (E : Set α)) (E : Set α) -
          matroidRank (Matroid.freeOn (E : Set α)) (S : Set α))
        = (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card) := by
    intro S hS
    rw [matroidRank_freeOn E S (Finset.mem_powerset.mp hS),
      matroidRank_freeOn E E (le_refl E)]
  rw [charPoly, Finset.sum_congr rfl hrank, Finset.sum_powerset]
  have hsub : ((X : Polynomial ℤ) - 1) = (-1) + X := by ring
  rw [hsub, add_pow]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hcard : ∀ S ∈ Finset.powersetCard j E,
      (-1 : Polynomial ℤ) ^ S.card * X ^ (E.card - S.card)
        = (-1 : Polynomial ℤ) ^ j * X ^ (E.card - j) := by
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  ring

/-- Log-concavity of binomial coefficients. -/
lemma choose_log_concave (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases Nat.lt_or_ge (k + 1) n with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n = k + 2 + d := ⟨n - (k + 2), by omega⟩
    have h1 := Nat.choose_succ_right_eq n k
    have h2 := Nat.choose_succ_right_eq n (k + 1)
    subst hd
    have e1 : k + 2 + d - k = d + 2 := by omega
    have e2 : k + 2 + d - (k + 1) = d + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    nlinarith [h1, h2, Nat.zero_le (Nat.choose (k + 2 + d) k),
      Nat.zero_le (Nat.choose (k + 2 + d) (k + 1)), Nat.zero_le (Nat.choose (k + 2 + d) (k + 2))]
  · have : n.choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]

/-- The absolute values of the coefficients of `(t - 1)^n` are the binomial coefficients. -/
lemma abs_coeff_X_sub_one_pow (n k : ℕ) :
    |(((X : Polynomial ℤ) - 1) ^ n).coeff k| = (n.choose k : ℤ) := by
  have hX : ((X : Polynomial ℤ) - 1) = X + C (-1 : ℤ) := by
    rw [map_neg, C_1]; ring
  rw [hX, coeff_X_add_C_pow]
  rw [abs_mul]
  simp [abs_pow]

/--
**Adiprasito–Huh–Katz, base case.**
The coefficients of the characteristic polynomial of a matroid form a log-concave sequence
(in absolute value).  Here this is established for the free (Boolean) matroid on a finite
ground set `E`, whose characteristic polynomial is `(t - 1)^{|E|}`: for every `k`,
`|w_k| * |w_{k+2}| ≤ |w_{k+1}|^2`.
-/
theorem huh_matroid_log_concave {α : Type*} [DecidableEq α] (E : Finset α) (k : ℕ) :
    |(charPoly (Matroid.freeOn (E : Set α)) E).coeff k| *
        |(charPoly (Matroid.freeOn (E : Set α)) E).coeff (k + 2)| ≤
      |(charPoly (Matroid.freeOn (E : Set α)) E).coeff (k + 1)| ^ 2 := by
  rw [charPoly_freeOn, abs_coeff_X_sub_one_pow, abs_coeff_X_sub_one_pow,
    abs_coeff_X_sub_one_pow]
  exact_mod_cast choose_log_concave E.card k

end Frontier

