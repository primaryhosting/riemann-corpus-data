/-
  Brockian/EquidistributionFiniteScaffold.lean

  Finite, unconditional support/counting consequences around the honest
  `PrimePairAsymptotic` schema.  This file deliberately does not prove prime
  equidistribution.  It only proves the finite bookkeeping needed to separate:

    * residue-support facts that are unconditional, apart from explicit finite
      "all counted pairs are above q" hypotheses, and
    * finite error bounds that follow from an already-supplied
      `PrimePairAsymptotic`.

  The analytic HL/BV-strength premise remains exactly where
  `Brockian.EquidistributionSchema` puts it.
-/
import Brockian.EquidistributionSchema

set_option autoImplicit false

open Finset
open Brockian.Admissibility

namespace Brockian.Equidistribution.FiniteScaffold

/-- The finite set of starts `p ≤ N` for gap-`g` prime pairs, before sorting by
residue class. -/
def pairStarts (N g : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (p + g))

/-- The honest total number of gap-`g` prime-pair starts `p ≤ N`, before sorting
by residue class. -/
def pairCount (N g : ℕ) : ℕ :=
  (pairStarts N g).card

@[simp] theorem mem_pairStarts {N g p : ℕ} :
    p ∈ pairStarts N g ↔ p ≤ N ∧ Nat.Prime p ∧ Nat.Prime (p + g) := by
  unfold pairStarts
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨Nat.le_of_lt_succ h.1, h.2⟩
  · intro h
    exact ⟨Nat.lt_succ_of_le h.1, h.2⟩

/-- The per-residue configuration count is bounded by the raw finite search
window. This is a finite counting fact, not an equidistribution statement. -/
theorem configCount_le_window (N q g : ℕ) [NeZero q] (a : ZMod q) :
    Brockian.Equidistribution.configCount N q g a ≤ N + 1 := by
  unfold Brockian.Equidistribution.configCount
  exact
    (Finset.card_filter_le
      (s := Finset.range (N + 1))
      (p := fun p => Nat.Prime p ∧ Nat.Prime (p + g) ∧ (p : ZMod q) = a)).trans_eq
      (Finset.card_range (N + 1))

/-- Summing `configCount` over all residues partitions the honest prime-pair
count. Each prime-pair start contributes to exactly one residue class modulo `q`. -/
theorem sum_configCount_univ_eq_pairCount (N q g : ℕ) [NeZero q] :
    (∑ a : ZMod q, Brockian.Equidistribution.configCount N q g a) = pairCount N g := by
  classical
  let s : Finset ℕ := pairStarts N g
  have hmaps : (s : Set ℕ).MapsTo (fun p : ℕ => (p : ZMod q)) (Finset.univ : Finset (ZMod q)) := by
    intro p hp
    simp
  have hpart :
      #s = ∑ a : ZMod q, (s.filter (fun p : ℕ => (p : ZMod q) = a)).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (f := fun p : ℕ => (p : ZMod q))
        (s := s)
        (t := (Finset.univ : Finset (ZMod q)))
        hmaps)
  change (∑ a : ZMod q, Brockian.Equidistribution.configCount N q g a) = #s
  rw [hpart]
  refine Finset.sum_congr rfl ?_
  intro a ha
  dsimp [s, pairStarts, Brockian.Equidistribution.configCount]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, and_assoc]

/-- A non-admissible residue has zero count once the finite search range is known
to contain only prime pairs with both endpoints above the modulus. The hypothesis
is intentionally explicit: this removes small-prime edge effects without asserting
any asymptotic prime equidistribution. -/
theorem configCount_eq_zero_of_not_admissible_of_large_pairs
    {N q g : ℕ} [NeZero q] {a : ZMod q} (hq : 2 ≤ q)
    (hlarge : ∀ p, p ≤ N → Nat.Prime p → Nat.Prime (p + g) → q < p ∧ q < p + g)
    (ha : a ∉ admissibleResidues q (g : ZMod q)) :
    Brockian.Equidistribution.configCount N q g a = 0 := by
  unfold Brockian.Equidistribution.configCount
  rw [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  rcases hp with ⟨hpRange, hpPrime, hpgPrime, hpResidue⟩
  have hpN : p ≤ N := by omega
  have hgt := hlarge p hpN hpPrime hpgPrime
  have hadm :
      (p : ZMod q) ∈ admissibleResidues q (g : ZMod q) :=
    Brockian.Equidistribution.prime_pair_config_admissible hq hpPrime hpgPrime hgt.1 hgt.2
  exact ha (by simpa [hpResidue] using hadm)

/-- Under the same explicit finite largeness condition, the admissible-residue
total is the full prime-pair count: outside the admissible support all residue
counts are zero. -/
theorem totalConfigCount_eq_pairCount_of_large_pairs
    {N q g : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hlarge : ∀ p, p ≤ N → Nat.Prime p → Nat.Prime (p + g) → q < p ∧ q < p + g) :
    Brockian.Equidistribution.totalConfigCount N q g = pairCount N g := by
  classical
  unfold Brockian.Equidistribution.totalConfigCount
  rw [← sum_configCount_univ_eq_pairCount N q g]
  exact Finset.sum_subset (by intro a ha; simp) (fun a _ ha =>
    configCount_eq_zero_of_not_admissible_of_large_pairs hq hlarge ha)

/-- The admissible-residue total is bounded by `(number of admissible residues) *
(N+1)`. This is purely finite bookkeeping. -/
theorem totalConfigCount_le_admissible_card_mul_window
    (N q g : ℕ) [NeZero q] :
    Brockian.Equidistribution.totalConfigCount N q g
      ≤ (admissibleResidues q (g : ZMod q)).card * (N + 1) := by
  unfold Brockian.Equidistribution.totalConfigCount
  exact Finset.sum_le_card_nsmul _ _ _ (fun a ha => configCount_le_window N q g a)

/-- When the gap is nonzero modulo `q`, the previous finite bound becomes
`(q - 2) * (N + 1)`. -/
theorem totalConfigCount_le_q_sub_two_mul_window
    (N q g : ℕ) [NeZero q] (hg : (g : ZMod q) ≠ 0) :
    Brockian.Equidistribution.totalConfigCount N q g ≤ (q - 2) * (N + 1) := by
  rw [← universal_admissibility_count q (g : ZMod q) hg]
  exact totalConfigCount_le_admissible_card_mul_window N q g

/-- The finite per-configuration error bound is exactly the field supplied by a
`PrimePairAsymptotic`. This theorem exists to make later finite arguments cite the
field without unfolding the structure. -/
theorem configCount_deviation_bound
    {q : ℕ} [NeZero q] {g : ℕ}
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g)
    {a : ZMod q} (ha : a ∈ admissibleResidues q (g : ZMod q)) (N : ℕ) :
    |(Brockian.Equidistribution.configCount N q g a : ℝ)
        - H.C * H.mainTerm N / ((q : ℝ) - 2)| ≤ H.err N :=
  H.count_asymptotic a ha N

/-- Finite total-error bound obtained by summing the uniform per-configuration
bound over the exactly `q - 2` admissible configurations. This is the finite
counting part of the quotient-limit proof, exposed separately. -/
theorem totalConfigCount_deviation_bound
    {q : ℕ} [NeZero q] {g : ℕ} (hq : 2 < q)
    (H : Brockian.Equidistribution.PrimePairAsymptotic q g) (N : ℕ) :
    |(Brockian.Equidistribution.totalConfigCount N q g : ℝ) - H.C * H.mainTerm N|
      ≤ ((q : ℝ) - 2) * H.err N := by
  have hq2ne : ((q : ℝ) - 2) ≠ 0 := by
    have hq2 : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  have hcard : (admissibleResidues q (g : ZMod q)).card = q - 2 :=
    universal_admissibility_count q (g : ZMod q) H.gap_ne
  have hcardR : ((admissibleResidues q (g : ZMod q)).card : ℝ) = (q : ℝ) - 2 := by
    rw [hcard, Nat.cast_sub (by omega)]
    norm_num
  have hcast : (Brockian.Equidistribution.totalConfigCount N q g : ℝ)
      = ∑ b ∈ admissibleResidues q (g : ZMod q),
          (Brockian.Equidistribution.configCount N q g b : ℝ) := by
    unfold Brockian.Equidistribution.totalConfigCount
    rw [Nat.cast_sum]
  have hsum_const :
      ∑ _b ∈ admissibleResidues q (g : ZMod q),
          H.C * H.mainTerm N / ((q : ℝ) - 2)
        = H.C * H.mainTerm N := by
    rw [Finset.sum_const, nsmul_eq_mul, hcardR, ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hq2ne
  rw [hcast]
  have hkey :
      (∑ b ∈ admissibleResidues q (g : ZMod q),
          (Brockian.Equidistribution.configCount N q g b : ℝ))
          - H.C * H.mainTerm N
        = ∑ b ∈ admissibleResidues q (g : ZMod q),
            ((Brockian.Equidistribution.configCount N q g b : ℝ)
              - H.C * H.mainTerm N / ((q : ℝ) - 2)) := by
    rw [Finset.sum_sub_distrib, hsum_const]
  rw [hkey]
  calc
    |∑ b ∈ admissibleResidues q (g : ZMod q),
        ((Brockian.Equidistribution.configCount N q g b : ℝ)
          - H.C * H.mainTerm N / ((q : ℝ) - 2))|
        ≤ ∑ b ∈ admissibleResidues q (g : ZMod q),
            |(Brockian.Equidistribution.configCount N q g b : ℝ)
              - H.C * H.mainTerm N / ((q : ℝ) - 2)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ admissibleResidues q (g : ZMod q), H.err N :=
          Finset.sum_le_sum (fun b hb => H.count_asymptotic b hb N)
    _ = ((admissibleResidues q (g : ZMod q)).card : ℝ) * H.err N := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((q : ℝ) - 2) * H.err N := by rw [hcardR]

end Brockian.Equidistribution.FiniteScaffold
