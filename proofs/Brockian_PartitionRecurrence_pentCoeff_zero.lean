/-
  Brockian/PartitionRecurrence.lean — THE PARTITION RECURRENCE FROM THE
  (now UNCONDITIONAL) PENTAGONAL NUMBER THEOREM (Aug 2).

  The three upstream modules established, over `ℤ⟦X⟧`:

    * `FranklinFixedPoint.pentagonalNumberTheorem (n) : (genFun pstChar).coeff n = pentCoeff n`
      — Euler's pentagonal number theorem, UNCONDITIONAL (Franklin's involution is fully built).
      Here `genFun pstChar = ∏_{i≥1}(1 − Xⁱ)` and `pentCoeff n` is the coefficient of `xⁿ` in
      `∑_{k∈ℤ}(−1)ᵏ x^{g_k}`, `g_k = k(3k−1)/2`.
    * `RamanujanCongruence.partitionGF = genFun (fun _ _ => 1)` — the partition generating
      function, with `coeff_partitionGF n : partitionGF.coeff n = (p n : ℤ)`, `p n = #(Partition n)`.
    * `PentagonalPartition` — the arithmetic of the generalized pentagonal numbers.

  Since `partitionGF = ∏(1 − Xⁱ)⁻¹` is the RECIPROCAL of the Euler product `genFun pstChar`,
  their product is `1`. Extracting the `n`-th coefficient of that product identity turns the
  pentagonal number theorem into the classical Euler recurrence for the partition function.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `geo`                              — the geometric factor `∑_{k≥0} (X^{i+1})^k` for part `i+1`.
  * `geo_mul`                          — `geo i · (1 − X^{i+1}) = 1` (the per-part geometric-series
                                         identity, from `tsum_pow_mul_one_sub_of_constantCoeff_eq_zero`).
  * `factor_eq_geo`                    — the `i`-th Euler factor of `partitionGF` equals `geo i`.
  * `partitionGF_eq_tprod_geo`         — `partitionGF = ∏'ᵢ geo i`.
  * `partitionGF_mul_pentagonalProduct`— **the product identity** `partitionGF · genFun pstChar = 1`
                                         in `ℤ⟦X⟧`: the partition series is the multiplicative inverse
                                         of Euler's pentagonal product (`tprod_mul` factor-by-factor).
  * `pentCoeff_zero`                   — `pentCoeff 0 = 1` (the `k = 0`, `g_0 = 0` term).
  * `partition_pentagonal_convolution` — **THE RECURRENCE IN RAW CONVOLUTION FORM.** For `n ≥ 1`,
                                         `∑_{(i,j)∈antidiagonal n} p(i)·pentCoeff(j) = 0`.
                                         This is exactly the vanishing of the `n`-th coefficient of
                                         `partitionGF · genFun pstChar` for `n ≥ 1`.
  * `partition_pentagonal_convolution_range` — the same identity as a range sum:
                                         `∑_{k=0}^{n} p(k)·pentCoeff(n−k) = 0` for `n ≥ 1`.
  * `partition_recurrence`             — **THE PARTITION RECURRENCE**, `p(n)` isolated: for `n ≥ 1`,
                                         `(p n : ℤ) = − ∑_{k<n} p(k)·pentCoeff(n−k)`. Since every
                                         summand has `k < n`, this determines `p(n)` from strictly
                                         smaller values and the pentagonal coefficients.

  ## What is NOT proved
  * The FULLY pentagonal-INDEXED closed form
        `p(n) = ∑_{k≥1} (−1)^{k−1} (p(n − g_k) + p(n − g_{−k}))`
    is NOT formalized here. It is NOT an open problem: it follows from
    `partition_pentagonal_convolution` by a purely mechanical FINITE reindexing of the antidiagonal
    sum along the pentagonal support (using that `pentCoeff e = 0` unless `e = g_k` for some `k`, and
    pairing the arms `k` and `−k`). We deliberately ship the raw convolution + `partition_recurrence`
    rather than assert the reindexed shape we did not carry out. See the obstruction note below.
  * Ramanujan's congruence `p(5n+4) ≡ 0 (mod 5)` remains OPEN, exactly as documented in
    `RamanujanCongruence.lean`. The new (unconditional) pentagonal leverage does NOT reach it: the
    recurrence proved here is an identity over `ℤ` and carries no mod-5 dissection structure. We do
    NOT restate the self-equivalent conditional that was deliberately removed there; nothing about
    the congruence is claimed or assumed in this file.

  ## Precise remaining obstruction
  * For the pentagonal-indexed closed form: only the bookkeeping is missing — a bijection between
    the pentagonal support `{e ≤ n : ∃ k, g_k = e}` and the index set `{k : g_k ≤ n}`, plus the
    `k ↔ −k` pairing of signs. This is a finite, elementary reindex of already-proved content, not a
    Mathlib gap; it is simply not carried out in this module.
  * For Ramanujan `p(5n+4) ≡ 0 (mod 5)`: the obstruction is inherited verbatim from
    `RamanujanCongruence.lean` (no partition arithmetic mod a prime, no Jacobi identity / η-quotient
    5-dissection, no modular-forms `U₅` theory at Mathlib 4.32). The convolution identity here does
    not shorten that gap.
-/
import Mathlib
import Brockian.PentagonalPartition
import Brockian.PentagonalTheoremFranklin
import Brockian.FranklinFixedPoint
import Brockian.RamanujanCongruence

set_option autoImplicit false

namespace Brockian.PartitionRecurrence

open Nat.Partition PowerSeries PowerSeries.WithPiTopology Finset
open Brockian.PentagonalTheoremFranklin
open Brockian.FranklinFixedPoint
open Brockian.RamanujanCongruence
open scoped PowerSeries.WithPiTopology

/-! ### The per-part geometric factor -/

/-- The geometric series factor `∑_{k≥0} (X^{i+1})^k` contributed by the part `i+1` to the partition
generating function `∏_{i≥1}(1 − Xⁱ)⁻¹`. -/
noncomputable def geo (i : ℕ) : ℤ⟦X⟧ := ∑' k : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ k

/-- **Per-part geometric-series identity.** `geo i · (1 − X^{i+1}) = 1`: the geometric factor is the
inverse of the Euler factor `1 − X^{i+1}` (whose argument has zero constant term). -/
theorem geo_mul (i : ℕ) : geo i * (1 - X ^ (i + 1)) = 1 := by
  unfold geo
  exact tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
    (by rw [map_pow, constantCoeff_X, zero_pow (Nat.succ_ne_zero i)])

/-- The `i`-th factor of `partitionGF` (as produced by `genFun_eq_tprod` at the all-ones character)
equals the geometric factor `geo i`: splitting off the `k = 0` term of `geo i` recovers
`1 + ∑_{j} X^{(i+1)(j+1)}`. -/
theorem factor_eq_geo (i : ℕ) :
    (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ ((i + 1) * (j + 1))) = geo i := by
  have hc : (X ^ (i + 1) : ℤ⟦X⟧).constantCoeff = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow (Nat.succ_ne_zero i)]
  have hsum : Summable (fun k : ℕ => (X ^ (i + 1) : ℤ⟦X⟧) ^ k) :=
    summable_pow_of_constantCoeff_eq_zero hc
  unfold geo
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hsum), pow_zero]
  congr 1
  apply tsum_congr
  intro k
  rw [one_smul, pow_mul]

/-- `partitionGF = ∏'ᵢ geo i`: the partition generating function is the infinite product of the
per-part geometric factors. -/
theorem partitionGF_eq_tprod_geo : partitionGF = ∏' i : ℕ, geo i := by
  unfold partitionGF
  rw [genFun_eq_tprod]
  refine tprod_congr (fun i => ?_)
  exact factor_eq_geo i

/-- **The product identity.** `partitionGF · genFun pstChar = 1` in `ℤ⟦X⟧`: the partition
generating function is the multiplicative inverse of Euler's pentagonal product `∏(1 − Xⁱ)`. Proved
factor-by-factor — each geometric factor times its Euler factor is `1` (`geo_mul`), so the infinite
products multiply to `1` (`Multipliable.tprod_mul`). -/
theorem partitionGF_mul_pentagonalProduct :
    partitionGF * genFun pstChar = 1 := by
  have hmgeo : Multipliable (fun i : ℕ => geo i) :=
    (multipliable_genFun (fun _ _ => (1 : ℤ))).congr (fun i => factor_eq_geo i)
  have hmsub : Multipliable (fun n : ℕ => (1 : ℤ⟦X⟧) - X ^ (n + 1)) :=
    multipliable_one_sub_X_pow ℤ
  rw [partitionGF_eq_tprod_geo, genFun_pstChar_eq_prod,
      ← Multipliable.tprod_mul hmgeo hmsub, tprod_congr geo_mul, tprod_one]

/-! ### The base coefficient `pentCoeff 0 = 1` -/

/-- `pentCoeff 0 = 1`: the exponent `0 = g_0` is generalized-pentagonal at the even index `k = 0`,
so its coefficient is `(−1)^0 = 1`. This is the `p(n)` term that gets isolated in the recurrence. -/
theorem pentCoeff_zero : pentCoeff 0 = 1 := by
  have h0 : pentagonal (0 : ℤ) = 0 := by
    have h : (pentagonal (0 : ℤ) : ℤ) = 0 := by simp [natCast_pentagonal]
    exact_mod_cast h
  have hex : ∃ k : ℤ, pentagonal k = 0 := ⟨0, h0⟩
  have hchoose : hex.choose = 0 :=
    pentagonal_injective (by rw [hex.choose_spec, h0])
  have hev : Even (0 : ℤ) := ⟨0, by ring⟩
  unfold pentCoeff
  rw [dif_pos hex, hchoose]
  unfold pentSign
  rw [if_pos hev]

/-! ### The partition recurrence -/

/-- **The Euler partition recurrence, raw convolution form.** For `n ≥ 1`,
`∑_{(i,j) ∈ antidiagonal n} p(i)·pentCoeff(j) = 0`. This is exactly the statement that the `n`-th
coefficient (`n ≥ 1`) of `partitionGF · genFun pstChar = 1` vanishes, with the two factors read off
by `coeff_partitionGF` and `pentagonalNumberTheorem`. This IS the pentagonal recurrence for the
partition function, in un-reindexed form. -/
theorem partition_pentagonal_convolution (n : ℕ) (hn : 1 ≤ n) :
    ∑ q ∈ antidiagonal n, (p q.1 : ℤ) * pentCoeff q.2 = 0 := by
  have key : PowerSeries.coeff n (partitionGF * genFun pstChar)
      = ∑ q ∈ antidiagonal n, (p q.1 : ℤ) * pentCoeff q.2 := by
    rw [coeff_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [coeff_partitionGF, pentagonalNumberTheorem]
  rw [partitionGF_mul_pentagonalProduct, coeff_one, if_neg (by omega)] at key
  exact key.symm

/-- **The recurrence as a range sum.** For `n ≥ 1`, `∑_{k=0}^{n} p(k)·pentCoeff(n−k) = 0`. -/
theorem partition_pentagonal_convolution_range (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (p k : ℤ) * pentCoeff (n - k) = 0 := by
  have h := partition_pentagonal_convolution n hn
  rwa [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun q : ℕ × ℕ => (p q.1 : ℤ) * pentCoeff q.2) n] at h

/-- **THE PARTITION RECURRENCE.** For `n ≥ 1`,
`(p n : ℤ) = − ∑_{k<n} p(k)·pentCoeff(n−k)`. Isolating the `k = n` term (`pentCoeff 0 = 1`) of the
range convolution expresses `p(n)` in terms of strictly smaller partition numbers weighted by the
pentagonal coefficients — Euler's recurrence for the partition function. -/
theorem partition_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (p n : ℤ) = - ∑ k ∈ range n, (p k : ℤ) * pentCoeff (n - k) := by
  have h := partition_pentagonal_convolution_range n hn
  rw [Finset.sum_range_succ, Nat.sub_self, pentCoeff_zero, mul_one] at h
  linarith [h]

end Brockian.PartitionRecurrence
