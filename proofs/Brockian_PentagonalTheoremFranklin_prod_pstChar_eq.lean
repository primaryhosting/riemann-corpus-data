/-
  Brockian/PentagonalTheoremFranklin.lean — THE PENTAGONAL NUMBER THEOREM,
  reduced to Franklin's involution (Aug 1).

  `Brockian/PentagonalPartition.lean` proved the ARITHMETIC SPINE of Euler's
  pentagonal number theorem (the generalized pentagonal numbers g_k = k(3k−1)/2,
  their exact doubling law, injectivity ⇒ distinct exponents, and p(0)=1). It
  left OPEN the theorem itself:

        ∏_{n≥1} (1 − xⁿ)  =  ∑_{k∈ℤ} (−1)ᵏ x^{g_k}.

  This module pushes that program to the exact frontier reachable at Mathlib
  4.32. Mathlib provides the generating-function apparatus for partitions
  (`Nat.Partition.genFun`, `genFun_eq_tprod`, `distincts`) and the pentagonal
  function `pentagonal : ℤ → ℕ` — but its `Pentagonal.lean` explicitly lists the
  pentagonal number theorem as a `TODO`, and Franklin's sign-reversing
  involution is ABSENT from the library.

  We do the honest thing: we PROVE the entire chain up to Franklin, isolating the
  one missing combinatorial fact as a single, precisely-stated named hypothesis.

  The engine is a character choice. For `pstChar i c = if c = 1 then −1 else 0`,
  Mathlib's `genFun pstChar` is (proved here) exactly the pentagonal product
  `∏_{i≥1}(1 − xⁱ)`, and its `n`-th coefficient is (proved here) the SIGNED COUNT

        ∑_{p ⊢ n, p distinct} (−1)^{#parts(p)}

  (partitions into an even number of distinct parts, minus those into an odd
  number). Franklin's number-theoretic theorem is precisely the assertion that
  this signed count collapses to `(−1)ᵏ` when `n = g_k` and to `0` otherwise —
  i.e. it equals `pentCoeff n`. THAT collapse is the sole remaining obstruction,
  named `hFranklin` below. It is a TRUE statement (so the conditional theorems are
  not vacuous), but proving it requires constructing Franklin's involution, which
  Mathlib does not have.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `pstChar`                    — the Euler-product character `if c = 1 then −1 else 0`.
  * `prod_pstChar_eq`            — for a partition `p`, the character product equals
                                   `(−1)^{#parts}` if `p` has distinct parts, else `0`
                                   (a non-distinct partition contributes nothing).
  * `coeff_genFun_pstChar`       — **the coefficient identity**: the `n`-th coefficient of
                                   `genFun pstChar` equals `∑_{p ∈ distincts n} (−1)^{#parts}`.
  * `genFun_pstChar_eq_prod`     — **the product identity**: `genFun pstChar = ∏'ᵢ (1 − Xⁱ⁺¹)`,
                                   i.e. `genFun pstChar` really IS Euler's pentagonal product
                                   `∏_{n≥1}(1 − xⁿ)` in `ℤ⟦X⟧`.
  * `natCast_pentagonal_eq_pent` — bridge: Mathlib's `pentagonal k` (ℕ) cast to ℤ equals the
                                   repo's own `Brockian.PentagonalPartition.pent k`.
  * `pentSign`, `pentCoeff`      — the RHS coefficient `(−1)ᵏ` at `g_k`, else `0` (well-defined
                                   because `pentagonal` is injective).
  * `pentagonalNumberTheorem_of_franklin`  — **PST, conditional on Franklin.** Given the named
                                   hypothesis `hFranklin` (the signed distinct-count equals
                                   `pentCoeff`), the coefficient of `genFun pstChar` is `pentCoeff n`.
  * `pentagonalProduct_coeff_of_franklin`  — the same conclusion phrased on the actual product
                                   `∏'ᵢ(1 − Xⁱ⁺¹)`, via the product identity.

  ## What is NOT proved  (the single remaining obstruction)
  * `hFranklin` itself — Franklin's sign-reversing involution. Concretely, the statement
        `∀ m, (∑ p ∈ Nat.Partition.distincts m, (−1)^{#parts p}) = pentCoeff m`
    is TRUE but UNPROVED here. It is the assertion that the involution on distinct
    partitions (move the smallest part vs. peel the top diagonal) pairs off all
    distinct partitions of `m` with opposite `(−1)^{#parts}` sign, except for the two
    pentagonal fixed-point families, which survive with sign `(−1)ᵏ`. This is why the
    two theorems above are stated with `hFranklin` as an explicit hypothesis and are
    named `..._of_franklin` — they are NOT the unconditional theorem.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  Mathlib 4.32 has NO sign-reversing involution on `Nat.Partition.distincts` and no
  form of the pentagonal number theorem (`Mathlib/Combinatorics/Enumerative/Pentagonal.lean`
  states it as a `TODO`). The missing lemma is exactly:

      theorem franklin (m : ℕ) :
          (∑ p ∈ Nat.Partition.distincts m, (-1 : ℤ) ^ (Multiset.card p.parts))
            = pentCoeff m

  Proving it needs: (i) the Durfee/staircase statistics `s(p)` = smallest part and
  `t(p)` = length of the top boundary diagonal on a distinct partition; (ii) the
  Franklin map that either removes the smallest part and lengthens the diagonal, or
  the reverse, changing `#parts` by exactly one (hence flipping the sign); (iii) the
  proof that this map is an involution whose only fixed points occur when `s = t` (or
  `s = t+1`) with `m = g_k`, forcing all non-pentagonal signed contributions to
  cancel. None of this data exists in Mathlib; constructing it is a substantial
  combinatorial development beyond a single module.
-/
import Mathlib
import Brockian.PentagonalPartition

set_option autoImplicit false

namespace Brockian.PentagonalTheoremFranklin

open Nat.Partition PowerSeries Finset

/-- The Euler-product character `f(i, c) = if c = 1 then −1 else 0`. Feeding this to
Mathlib's `Nat.Partition.genFun` builds the pentagonal product `∏(1 − xⁱ)`: the factor
for part `i` becomes `1 + (−1)·xⁱ = 1 − xⁱ`, and only partitions with all parts
distinct (every count `= 1`) survive with a nonzero character product. -/
def pstChar : ℕ → ℕ → ℤ := fun _ c => if c = 1 then (-1 : ℤ) else 0

/-- The character product over a partition `p`: it equals `(−1)^{#parts}` when the parts
are all distinct, and `0` otherwise (a repeated part gives a `0` factor). This is the
combinatorial heart of the Euler product: only distinct partitions contribute, each
weighted by the parity of its number of parts. -/
theorem prod_pstChar_eq {n : ℕ} (p : n.Partition) :
    p.parts.toFinsupp.prod pstChar =
      if p.parts.Nodup then (-1 : ℤ) ^ (Multiset.card p.parts) else 0 := by
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  by_cases h : p.parts.Nodup
  · rw [if_pos h]
    have hval : ∀ i ∈ p.parts.toFinset, pstChar i (p.parts.count i) = (-1 : ℤ) := by
      intro i hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_one_of_mem h hi]
      simp [pstChar]
    rw [Finset.prod_congr rfl hval, Finset.prod_const, Multiset.toFinset_card_of_nodup h]
  · rw [if_neg h]
    rw [Multiset.nodup_iff_count_le_one] at h
    simp only [not_forall, not_le] at h
    obtain ⟨a, ha⟩ := h
    refine Finset.prod_eq_zero (i := a) ?_ ?_
    · rw [Multiset.mem_toFinset]
      exact Multiset.count_pos.mp (by omega)
    · have hne : p.parts.count a ≠ 1 := by omega
      simp [pstChar, hne]

/-- **The coefficient identity.** The `n`-th coefficient of `genFun pstChar` is the signed
count of partitions of `n` into distinct parts, weighted by `(−1)^{#parts}`. Equivalently:
`#{distinct partitions of n with an even number of parts} − #{… odd number of parts}`.
This is exactly the coefficient of `xⁿ` in Euler's product `∏_{i≥1}(1 − xⁱ)`. -/
theorem coeff_genFun_pstChar (n : ℕ) :
    (genFun pstChar).coeff n = ∑ p ∈ distincts n, (-1 : ℤ) ^ (Multiset.card p.parts) := by
  rw [coeff_genFun]
  simp_rw [prod_pstChar_eq]
  rw [distincts, Finset.sum_filter]

open scoped PowerSeries.WithPiTopology in
/-- **The product identity.** `genFun pstChar` is literally Euler's pentagonal product
`∏_{i≥1}(1 − xⁱ)` in `ℤ⟦X⟧`. Together with `coeff_genFun_pstChar`, this shows the
coefficient of `xⁿ` in `∏(1 − xⁱ)` is the signed distinct-partition count. -/
theorem genFun_pstChar_eq_prod :
    genFun pstChar = ∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) := by
  rw [genFun_eq_tprod]
  refine tprod_congr (fun i => ?_)
  rw [sub_eq_add_neg]
  congr 1
  rw [tsum_eq_single 0]
  · rw [smul_eq_C_mul]
    simp [pstChar]
  · intro j hj
    rw [smul_eq_C_mul]
    simp [pstChar, hj]

/-- Bridge to the repo's own definition: Mathlib's `pentagonal k` (an `ℕ`), cast to `ℤ`,
equals `Brockian.PentagonalPartition.pent k = k(3k−1)/2`. This ties the exponents used
here to the injective generalized-pentagonal function proved in `PentagonalPartition`. -/
theorem natCast_pentagonal_eq_pent (k : ℤ) :
    (pentagonal k : ℤ) = Brockian.PentagonalPartition.pent k := by
  rw [natCast_pentagonal]; rfl

/-- The sign `(−1)ᵏ` attached to the exponent `g_k`. -/
def pentSign (k : ℤ) : ℤ := if Even k then 1 else -1

open Classical in
/-- The right-hand-side coefficient of the pentagonal number theorem: the coefficient of
`xⁿ` in `∑_{k∈ℤ} (−1)ᵏ x^{g_k}`. Because `pentagonal` is injective (Mathlib's
`pentagonal_injective`, matching `PentagonalPartition.pent_injective`), at most one `k`
has `g_k = n`, so this is `(−1)ᵏ` when `n` is generalized-pentagonal with index `k`, and
`0` otherwise. -/
noncomputable def pentCoeff (n : ℕ) : ℤ :=
  if h : ∃ k : ℤ, pentagonal k = n then pentSign h.choose else 0

/-- **The pentagonal number theorem, conditional on Franklin's involution.**

Given `hFranklin` — the single missing combinatorial fact that the signed distinct-partition
count equals `pentCoeff` — the `n`-th coefficient of `genFun pstChar` (i.e. of the pentagonal
product `∏(1 − xⁱ)`) equals `pentCoeff n`, the coefficient of `∑_{k}(−1)ᵏ x^{g_k}`.

This is NOT the unconditional theorem: `hFranklin` is a genuine, currently-unproved hypothesis
(see the module header for the precise obstruction). The proof here supplies everything EXCEPT
that involution. -/
theorem pentagonalNumberTheorem_of_franklin
    (hFranklin : ∀ m : ℕ,
      (∑ p ∈ distincts m, (-1 : ℤ) ^ (Multiset.card p.parts)) = pentCoeff m)
    (n : ℕ) : (genFun pstChar).coeff n = pentCoeff n := by
  rw [coeff_genFun_pstChar]
  exact hFranklin n

open scoped PowerSeries.WithPiTopology in
/-- The conditional pentagonal number theorem, phrased directly on Euler's product
`∏'ᵢ (1 − Xⁱ⁺¹) = ∏_{n≥1}(1 − xⁿ)` via the product identity. Same status: conditional on
`hFranklin`. -/
theorem pentagonalProduct_coeff_of_franklin
    (hFranklin : ∀ m : ℕ,
      (∑ p ∈ distincts m, (-1 : ℤ) ^ (Multiset.card p.parts)) = pentCoeff m)
    (n : ℕ) :
    (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff n = pentCoeff n := by
  rw [← genFun_pstChar_eq_prod]
  exact pentagonalNumberTheorem_of_franklin hFranklin n

end Brockian.PentagonalTheoremFranklin
