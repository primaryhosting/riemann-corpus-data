/-
  Brockian/RamanujanCongruence.lean — THE PARTITION GENERATING FUNCTION over ℤ,
  and Ramanujan's congruence p(5n+4) ≡ 0 (mod 5) documented as OPEN (Aug 2).

  The Euler↔five headline in this repo continues from the pentagonal number
  theorem (`PentagonalPartition.lean`, `PentagonalTheoremFranklin.lean`) toward
  Ramanujan's first partition congruence:

        p(5n + 4) ≡ 0   (mod 5)      for every n ≥ 0,

  where p is the ordinary partition function. The instances are
  p(4) = 5, p(9) = 30, p(14) = 135, p(19) = 490, … — each divisible by 5.

  This module establishes the genuine, unconditional BRIDGE between the ordinary
  partition function and Mathlib's generating-function machinery, and then states
  Ramanujan's congruence itself as OPEN, with the precise Mathlib-missing
  obstruction. We deliberately do NOT dress the congruence up as a "conditional
  theorem": the only hypothesis one could state without the missing theory (an
  integer power series G with `∑ p(5n+4)Xⁿ = 5·G`) is logically EQUIVALENT to the
  conclusion `∀ n, 5 ∣ p(5n+4)` (build G coefficient-wise), so such a conditional
  would be modus-ponens theater, not progress. What is honest is the bridge below.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `p`                       — the partition function p(n) = Fintype.card (Nat.Partition n).
  * `partitionGF`             — the partition generating function `genFun (fun _ _ => 1)` over ℤ,
                                i.e. `∑ p(n) Xⁿ = ∏_{i≥1} (1 − Xⁱ)⁻¹`.
  * `coeff_partitionGF`       — **the bridge**: the n-th coefficient of `partitionGF` equals
                                `(p n : ℤ)`. This identifies Mathlib's `genFun` at the all-ones
                                character with `∑ p(n) Xⁿ` — the honest, unconditional new content.
  * `coeff_partitionGF_zero`  — `partitionGF`'s constant term is 1, i.e. p(0) = 1, anchored on
                                `Nat.Partition`.
  * `five_dvd_of_dissection`  — a reusable divisibility read-off: if a natural number's ℤ-cast is
                                `5 * m`, then `5 ∣` it. (This is the ONLY step that would remain
                                trivial once the missing generating-function-mod-5 identity is in
                                hand; it is kept as a genuine general lemma, not as a fake gate.)

  ## What is NOT proved — Ramanujan's congruence itself is OPEN here
  * `p(5n+4) ≡ 0 (mod 5)` is NOT proved, and is NOT stated as any theorem or named hypothesis in
    this file. In particular there is NO `..._of_dissection` conditional: the natural "conditional"
    hypothesis (`∃ G : ℤ⟦X⟧, ∀ n, partitionGF.coeff (5n+4) = 5 * G.coeff n`) is logically
    EQUIVALENT to the conclusion, so packaging it as a theorem would be modus-ponens theater rather
    than progress. The congruence remains open at Mathlib 4.32.

  ## Precise remaining obstruction (exact missing Mathlib theory)
  Mathlib 4.32 has NO Ramanujan congruences and NO partition-function arithmetic mod a prime.
  Both known elementary routes need machinery absent from the library:
    (i)   the Frobenius/"freshman" congruence  `(∏(1−Xⁿ))⁵ ≡ ∏(1−X^{5n})  (mod 5)`  in `(ZMod 5)⟦X⟧`
          (needs the Frobenius endomorphism acting coefficient-wise on power series over `ZMod 5`);
    (ii)  Jacobi's identity  `∏(1−Xⁿ)³ = ∑_{k≥0}(−1)ᵏ(2k+1) X^{k(k+1)/2}`  — absent from Mathlib;
    (iii) the 5-dissection of  `X·∏(1−Xⁿ)⁴`  isolating the residue class: the arithmetic fact that
          `k(3k−1)/2 + j(j+1)/2 + 1 ≡ 0 (mod 5)` forces `2j+1 ≡ 0` and `k ≡ 0`, killing every
          `X^{5m}` coefficient mod 5;
    (iv)  transfer through the reciprocal (partition) generating function `∏(1−Xⁿ)⁻¹` treated
          coefficient-wise mod 5, to push the vanishing back onto p.
  The modern alternative — via the theory of modular forms (the weight of the `η`-quotient and the
  `U₅` Hecke operator) — needs a formalization of modular forms far beyond Mathlib 4.32. Even
  granting (i) alone (the Frobenius congruence, a real standalone sub-lemma), the reduction from it
  to the congruence still requires (ii)+(iii)+(iv); the reduction is NOT expressible as a single
  citable sub-lemma one could honestly assume here. Hence the congruence is left OPEN rather than
  fronted by an equivalent hypothesis.

  ## Relation to the pentagonal work in this repo
  `partitionGF` is the RECIPROCAL of the pentagonal product studied in
  `PentagonalTheoremFranklin.lean` (there, `genFun pstChar = ∏(1 − Xⁱ)`; here,
  `genFun (fun _ _ => 1) = ∏(1 − Xⁱ)⁻¹`). The mod-5 obstruction (iv) above is exactly the step of
  inverting that product coefficient-wise mod 5 — the honest seam between the two files.
-/
import Mathlib
import Brockian.PentagonalPartition

set_option autoImplicit false

namespace Brockian.RamanujanCongruence

open Nat.Partition PowerSeries Finset

/-- The ordinary partition function `p(n)`, as the number of partitions of `n`. This is exactly
Mathlib's `Fintype.card (Nat.Partition n)` (the partitions of `n` form a finite type). -/
def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The partition generating function `∑ p(n) Xⁿ = ∏_{i≥1} (1 − Xⁱ)⁻¹`, realized over `ℤ` as
Mathlib's `Nat.Partition.genFun` at the all-ones character `f(i,c) = 1`. With this character every
partition contributes weight `1`, so the n-th coefficient counts partitions of `n`. -/
noncomputable def partitionGF : ℤ⟦X⟧ := genFun (fun _ _ => (1 : ℤ))

/-- **The bridge.** The n-th coefficient of the partition generating function is `p(n)`, i.e.
Mathlib's `genFun` at the all-ones character really is `∑ p(n) Xⁿ`. This is the honest,
unconditional contact with real partition counting: each partition of `n` contributes the empty
product `1`, and there are `Fintype.card (Nat.Partition n)` of them. -/
theorem coeff_partitionGF (n : ℕ) : partitionGF.coeff n = (p n : ℤ) := by
  unfold partitionGF p
  rw [coeff_genFun]
  have hprod : ∀ q : n.Partition, q.parts.toFinsupp.prod (fun _ _ => (1 : ℤ)) = 1 := by
    intro q
    simp [Finsupp.prod]
  rw [Finset.sum_congr rfl (fun q _ => hprod q)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The constant term of the partition generating function is `1`, i.e. `p(0) = 1`: the empty
partition is the unique partition of `0`. Anchored on Mathlib's `Nat.Partition`. -/
theorem coeff_partitionGF_zero : partitionGF.coeff 0 = 1 := by
  rw [coeff_partitionGF]
  have : p 0 = 1 := by
    unfold p
    rw [Fintype.card_eq_one_iff_nonempty_unique]
    exact ⟨inferInstance⟩
  rw [this]; rfl

/-- Reusable divisibility read-off: if the ℤ-cast of a natural number `a` equals `5 * m` for some
integer `m`, then `5 ∣ a` in `ℕ`. This is the only step that would remain trivial once the missing
generating-function-mod-5 identity (see the module header) is available; it is stated as a genuine
general lemma, NOT as a gate whose hypothesis is equivalent to Ramanujan's congruence. -/
theorem five_dvd_of_dissection {a : ℕ} {m : ℤ} (h : (a : ℤ) = 5 * m) : 5 ∣ a := by
  have hz : (5 : ℤ) ∣ (a : ℤ) := ⟨m, h⟩
  have : ((5 : ℕ) : ℤ) ∣ ((a : ℕ) : ℤ) := by exact_mod_cast hz
  exact_mod_cast this

end Brockian.RamanujanCongruence
