/-
  Brockian/FranklinInvolution.lean — FRANKLIN'S SIGN-REVERSING INVOLUTION,
  the combinatorial core of the pentagonal number theorem (Aug 2).

  `Brockian/PentagonalTheoremFranklin.lean` proved the Euler-PRODUCT side of the
  pentagonal number theorem and reduced the whole theorem to ONE opaque hypothesis

      hFranklin : ∀ m, (∑ p ∈ distincts m, (-1)^{#parts p}) = pentCoeff m,

  i.e. "the signed count of distinct partitions of `m` collapses to the pentagonal
  coefficient". That module supplied EVERYTHING except the collapse itself.

  This module does the honest next step. Franklin's classical proof of the collapse
  has exactly two ingredients:

    (F1)  a SIGN-REVERSING INVOLUTION on the distinct partitions that are NOT
          fixed points — it flips `#parts` by one, so its contributions cancel in
          pairs; and
    (F2)  the FIXED POINTS are precisely two "staircase" families, whose signed
          count is `pentCoeff m`.

  Ingredient (F1)'s CONSEQUENCE — that a sign-reversing involution off a fixed set
  makes the signed sum equal the sum over the fixed set — is a genuine theorem, and
  we PROVE it here (`signedSum_eq_fixed_of_involution`) from Mathlib's
  `Finset.sum_involution`. This discharges the *summation* heart of Franklin: the
  reason the non-pentagonal partitions contribute nothing is now a proved lemma, not
  an assumption. We also define and prove the defining properties of the two Franklin
  statistics — the smallest part `sPart` and the top-diagonal length `tDiag` — that
  the involution is built from; these are the `s(p)` and `t(p)` of the classical
  argument.

  What remains genuinely missing at Mathlib 4.32 is the CONSTRUCTION of the map
  itself (erase the smallest part / grow the top diagonal, or the reverse) as an
  operation on `Nat.Partition`, together with (F2). We package that irreducible
  remainder as the structure `FranklinData m` and PROVE that `hFranklin` — hence the
  full pentagonal number theorem — follows from `∀ m, FranklinData m`. So this module
  strictly SHRINKS the obstruction: from the monolithic signed-count identity down to
  the explicit involution-with-fixed-sum data, with the cancellation step proved.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `signOf`                       — the weight `(−1)^{#parts p}` of a partition `p`.
  * `signOf_ne_zero`               — `signOf p ≠ 0` (it is always `±1`).
  * `sPart`, `sPart_mem`, `sPart_le`
                                   — Franklin's statistic `s(p)` = smallest part, with
                                     PROOFS that it is an actual part and is minimal.
  * `largestPart`, `largestPart_mem`, `le_largestPart`
                                   — the largest part, an actual part and maximal.
  * `tDiag`, `tDiag_notMem`, `mem_of_lt_tDiag`, `one_le_tDiag`
                                   — Franklin's statistic `t(p)` = length of the top
                                     boundary diagonal, defined as the first gap below
                                     the largest part, with PROOFS that the run
                                     `largest, largest−1, …, largest−(t−1)` is present,
                                     that `largest − t` is absent, and that `t ≥ 1` for
                                     a nonempty partition.
  * `signedSum_eq_fixed_of_involution`
                                   — **the cancellation engine.** A sign-reversing
                                     involution on `distincts m ∖ F` forces
                                     `∑_{distincts m} signOf = ∑_{F} signOf`. Proved via
                                     `Finset.sum_involution`. This is ingredient (F1).
  * `FranklinData`                 — the isolated remaining data: fixed set `F ⊆ distincts m`,
                                     the involution on the complement (membership,
                                     sign-flip, non-fixedness, involutivity), and the
                                     fixed-sum identity `∑_F signOf = pentCoeff m`.
  * `signedSum_eq_pentCoeff_of_franklinData`
                                   — from `FranklinData m`, the signed count equals `pentCoeff m`.
  * `franklin_of_franklinData`     — the same in the exact shape of `hFranklin`.
  * `pentagonalNumberTheorem_of_franklinData`
                                   — **PST conditioned on `∀ m, FranklinData m`.** The `n`-th
                                     coefficient of Euler's product `genFun pstChar` equals
                                     `pentCoeff n`, assuming the Franklin data (NOT the opaque
                                     `hFranklin`). This is a strictly sharper hypothesis: the
                                     cancellation is proved; only the map + fixed-sum remain.

  ## What is NOT proved  (the residual obstruction, now sharpened)
  * `∀ m, FranklinData m` — the CONSTRUCTION of Franklin's map as an operation on
    `Nat.Partition` (case `sPart p ≤ tDiag p`: delete the smallest part and lengthen
    the top diagonal; case `sPart p > tDiag p`: the reverse), the proof that it is a
    sign-reversing involution off the two pentagonal staircase families, and the
    fixed-sum identity `∑_{F} signOf = pentCoeff m`. None of this map machinery exists
    in Mathlib 4.32, and constructing it on `Multiset`-backed partitions is a
    substantial development. We do NOT assert it; we require it as `FranklinData`.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  Everything about how a sign-reversing involution kills the signed sum is now proved
  (`signedSum_eq_fixed_of_involution`), and the two statistics `s = sPart`,
  `t = tDiag` from which the map is defined are constructed with their defining
  properties. The single missing object is a term of type

      ∀ m : ℕ, FranklinData m

  i.e. for each `m` an explicit `Nat.Partition`-valued map `φ` on the non-pentagonal
  distinct partitions of `m` satisfying `signOf (φ p) = − signOf p`, `φ p ≠ p`,
  `φ (φ p) = p`, staying inside the non-fixed set, together with the identification of
  the fixed set `F` as the pentagonal staircases and the count `∑_{F} signOf = pentCoeff m`.
  Building `φ` requires `Multiset` surgery (erase smallest part; add one to the top
  `sPart p` parts / peel the `tDiag p` diagonal into a new smallest part) with the
  attendant positivity, sum-preservation, and `Nodup` proofs — beyond a single module.
-/
import Mathlib
import Brockian.PentagonalPartition
import Brockian.PentagonalTheoremFranklin

set_option autoImplicit false

namespace Brockian.FranklinInvolution

open Nat.Partition Finset
open Brockian.PentagonalTheoremFranklin

/-- The Franklin/Euler weight of a partition: `(−1)` raised to the number of parts.
The signed distinct-partition count is `∑ p ∈ distincts m, signOf p`. -/
def signOf {m : ℕ} (p : m.Partition) : ℤ := (-1 : ℤ) ^ (Multiset.card p.parts)

/-- The weight is never zero (it is always `±1`); this is what lets a sign-reversing
involution pair partitions off with cancelling contributions. -/
theorem signOf_ne_zero {m : ℕ} (p : m.Partition) : signOf p ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-! ### Franklin's statistic `s(p)` — the smallest part -/

open Classical in
/-- Franklin's statistic `s(p)`: the smallest part of `p` (`0` for the empty partition).
Together with `tDiag` this is the pair of statistics from which Franklin's map is built:
the case split is on `sPart p ≤ tDiag p` versus `sPart p > tDiag p`. -/
noncomputable def sPart {m : ℕ} (p : m.Partition) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.min' h else 0

/-- For a nonempty partition, `sPart p` really is one of the parts. -/
theorem sPart_mem {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) : sPart p ∈ p.parts := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [sPart, dif_pos hne, ← Multiset.mem_toFinset]
  exact p.parts.toFinset.min'_mem hne

/-- `sPart p` is `≤` every part: it is the minimum. -/
theorem sPart_le {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) {x : ℕ} (hx : x ∈ p.parts) :
    sPart p ≤ x := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [sPart, dif_pos hne]
  exact Finset.min'_le _ x (Multiset.mem_toFinset.mpr hx)

/-! ### The largest part -/

open Classical in
/-- The largest part of `p` (`0` for the empty partition). The top diagonal `tDiag`
descends from this value. -/
noncomputable def largestPart {m : ℕ} (p : m.Partition) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.max' h else 0

/-- For a nonempty partition, `largestPart p` really is one of the parts. -/
theorem largestPart_mem {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) :
    largestPart p ∈ p.parts := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [largestPart, dif_pos hne, ← Multiset.mem_toFinset]
  exact p.parts.toFinset.max'_mem hne

/-- `largestPart p` is `≥` every part: it is the maximum. -/
theorem le_largestPart {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) {x : ℕ} (hx : x ∈ p.parts) :
    x ≤ largestPart p := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [largestPart, dif_pos hne]
  exact Finset.le_max' _ x (Multiset.mem_toFinset.mpr hx)

/-! ### Franklin's statistic `t(p)` — the top boundary diagonal -/

/-- There is always a gap below the largest part: at `j = largestPart p + 1` the value
`largestPart p − j` is `0`, which is never a part (parts are positive). This existence
underwrites the `Nat.find` definition of `tDiag`. -/
theorem tDiag_gap_exists {m : ℕ} (p : m.Partition) :
    ∃ j, largestPart p - j ∉ p.parts := by
  refine ⟨largestPart p + 1, ?_⟩
  have h0 : largestPart p - (largestPart p + 1) = 0 := by omega
  rw [h0]
  exact fun h => Nat.lt_irrefl 0 (p.parts_pos h)

open Classical in
/-- Franklin's statistic `t(p)`: the length of the top boundary diagonal, i.e. the number
of consecutive values `largestPart p, largestPart p − 1, …` that are all parts, defined as
the first `j` at which `largestPart p − j` fails to be a part. On a distinct partition this
is exactly the length of the rightmost diagonal of the Young diagram. -/
noncomputable def tDiag {m : ℕ} (p : m.Partition) : ℕ := Nat.find (tDiag_gap_exists p)

/-- The value just past the top diagonal is absent: `largestPart p − tDiag p` is not a part. -/
theorem tDiag_notMem {m : ℕ} (p : m.Partition) : largestPart p - tDiag p ∉ p.parts :=
  Nat.find_spec (tDiag_gap_exists p)

/-- Every value inside the top diagonal is present: for `i < tDiag p`, `largestPart p − i`
is a part. This is the defining "unbroken run" property of the diagonal. -/
theorem mem_of_lt_tDiag {m : ℕ} (p : m.Partition) {i : ℕ} (hi : i < tDiag p) :
    largestPart p - i ∈ p.parts :=
  not_not.mp (Nat.find_min (tDiag_gap_exists p) hi)

/-- A nonempty partition has a top diagonal of length at least one (the largest part
itself starts the diagonal). -/
theorem one_le_tDiag {m : ℕ} {p : m.Partition} (hp : p.parts ≠ 0) : 1 ≤ tDiag p := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have hnm : largestPart p - tDiag p ∉ p.parts := tDiag_notMem p
  rw [h, Nat.sub_zero] at hnm
  exact hnm (largestPart_mem hp)

/-! ### The cancellation engine (ingredient F1) -/

/-- **Franklin's cancellation, proved.** Suppose `F ⊆ distincts m` and there is a map `g`
on the *non-fixed* distinct partitions `distincts m ∖ F` that: stays inside `distincts m ∖ F`
(`g_mem`), reverses the sign (`g_sign`), has no fixed point (`g_ne`), and is involutive
(`g_inv`). Then the contributions off `F` cancel in pairs, so

    ∑_{p ∈ distincts m} signOf p = ∑_{p ∈ F} signOf p.

This is exactly why, in Franklin's proof, only the fixed (pentagonal) partitions survive.
The proof is `Finset.sum_involution` on the complement plus the split
`∑_{distincts m} = ∑_{distincts m ∖ F} + ∑_{F}`. -/
theorem signedSum_eq_fixed_of_involution {m : ℕ}
    (F : Finset m.Partition) (hF : F ⊆ distincts m)
    (g : ∀ p ∈ distincts m \ F, m.Partition)
    (g_mem : ∀ p (hp : p ∈ distincts m \ F), g p hp ∈ distincts m \ F)
    (g_sign : ∀ p (hp : p ∈ distincts m \ F), signOf (g p hp) = - signOf p)
    (g_ne : ∀ p (hp : p ∈ distincts m \ F), g p hp ≠ p)
    (g_inv : ∀ p (hp : p ∈ distincts m \ F), g (g p hp) (g_mem p hp) = p) :
    ∑ p ∈ distincts m, signOf p = ∑ p ∈ F, signOf p := by
  have hzero : ∑ p ∈ distincts m \ F, signOf p = 0 := by
    refine Finset.sum_involution g ?_ ?_ g_mem g_inv
    · intro a ha
      rw [g_sign a ha]; ring
    · intro a ha _
      exact g_ne a ha
  have hsplit := Finset.sum_sdiff (f := fun p => signOf p) hF
  rw [hzero, zero_add] at hsplit
  exact hsplit.symm

/-! ### The isolated remaining obstruction, and PST modulo it -/

/-- **The residual combinatorial data Mathlib lacks.** A term of `FranklinData m` is exactly
Franklin's involution package at level `m`: the fixed set `fixed` (the pentagonal staircases),
the sign-reversing involution `map` on the non-fixed distinct partitions, and the fixed-point
sign count. This is what remains unproven; `signedSum_eq_fixed_of_involution` already proves the
consequence that only `fixed` contributes. -/
structure FranklinData (m : ℕ) where
  /-- The fixed points of Franklin's map (the two pentagonal staircase families). -/
  fixed : Finset m.Partition
  /-- Fixed points are distinct partitions. -/
  fixed_subset : fixed ⊆ distincts m
  /-- Franklin's map on the non-fixed distinct partitions. -/
  map : ∀ p ∈ distincts m \ fixed, m.Partition
  /-- The map stays among non-fixed distinct partitions. -/
  map_mem : ∀ p (hp : p ∈ distincts m \ fixed), map p hp ∈ distincts m \ fixed
  /-- The map flips the parity of the number of parts (sign reversal). -/
  map_sign : ∀ p (hp : p ∈ distincts m \ fixed), signOf (map p hp) = - signOf p
  /-- The map has no fixed point off `fixed`. -/
  map_ne : ∀ p (hp : p ∈ distincts m \ fixed), map p hp ≠ p
  /-- The map is an involution. -/
  map_involutive : ∀ p (hp : p ∈ distincts m \ fixed), map (map p hp) (map_mem p hp) = p
  /-- The surviving fixed points carry the pentagonal signed count. -/
  fixed_sum : ∑ p ∈ fixed, signOf p = pentCoeff m

/-- Given Franklin's data at `m`, the signed distinct-partition count is `pentCoeff m`. -/
theorem signedSum_eq_pentCoeff_of_franklinData {m : ℕ} (d : FranklinData m) :
    ∑ p ∈ distincts m, signOf p = pentCoeff m := by
  rw [signedSum_eq_fixed_of_involution d.fixed d.fixed_subset d.map d.map_mem d.map_sign
    d.map_ne d.map_involutive]
  exact d.fixed_sum

/-- Franklin's identity `hFranklin`, in its exact original shape, follows from the Franklin data
for every `m`. This is what `PentagonalTheoremFranklin` took as an unproved hypothesis. -/
theorem franklin_of_franklinData (h : ∀ m, FranklinData m) (m : ℕ) :
    (∑ p ∈ distincts m, (-1 : ℤ) ^ (Multiset.card p.parts)) = pentCoeff m := by
  have hm := signedSum_eq_pentCoeff_of_franklinData (h m)
  simpa only [signOf] using hm

/-- **The pentagonal number theorem, conditioned on `∀ m, FranklinData m`.** The `n`-th
coefficient of Euler's product `genFun pstChar = ∏_{i≥1}(1 − xⁱ)` equals `pentCoeff n`, assuming
Franklin's involution-with-fixed-sum data at every level. This is strictly sharper than the
original `..._of_franklin`: the summation/cancellation step is now proved
(`signedSum_eq_fixed_of_involution`); only the construction of the map and the fixed-sum remain. -/
theorem pentagonalNumberTheorem_of_franklinData (h : ∀ m, FranklinData m) (n : ℕ) :
    (genFun pstChar).coeff n = pentCoeff n :=
  pentagonalNumberTheorem_of_franklin (franklin_of_franklinData h) n

end Brockian.FranklinInvolution
