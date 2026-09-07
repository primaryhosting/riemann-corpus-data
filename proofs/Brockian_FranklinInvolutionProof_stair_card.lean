/-
  Brockian/FranklinInvolutionProof.lean — DISCHARGING FRANKLIN'S FIXED POINTS,
  and isolating the involution map (Aug 2).

  `Brockian/FranklinInvolution.lean` proved Franklin's CANCELLATION ENGINE
  (`signedSum_eq_fixed_of_involution`) and reduced the whole pentagonal number
  theorem to a term of the structure `FranklinData m`. That structure has two
  logically separate ingredients, mirroring Franklin's classical proof:

    (F1) the sign-reversing INVOLUTION `map` on the non-fixed distinct partitions
         (its four properties: `map_mem`, `map_sign`, `map_ne`, `map_involutive`);
    (F2) the FIXED SET `fixed` — the two pentagonal staircases — together with the
         identity `∑_{fixed} signOf = pentCoeff m`.

  THIS MODULE PROVES (F2) OUTRIGHT and pins (F1) down to a single named object.

  Concretely: for each integer index `k` we construct the Franklin staircase
  `stair k` — the multiset of parts of the fixed-point partition at index `k`:

      k > 0 :  {k, k+1, …, 2k−1}   (k parts, sum g_k          = pentagonal k)
      k < 0 :  {r+1, …, 2r}        (r = −k parts, sum g_{−r} = pentagonal k)
      k = 0 :  {}                   (empty, sum 0              = pentagonal 0)

  We prove it has `k.natAbs` parts, is `Nodup` (distinct), is positive, and — the
  arithmetic heart — SUMS TO `pentagonal k` (the generalized pentagonal number
  `g_k = k(3k−1)/2`). From this we build the fixed set `fixedPart m` (the single
  staircase realizing `m` when `m` is pentagonal, else `∅`) and PROVE the two
  remaining `FranklinData` fixed-set fields honestly:

    * `fixedPart_subset : fixedPart m ⊆ distincts m`   (they are distinct partitions)
    * `fixedPart_sum    : ∑_{fixedPart m} signOf = pentCoeff m`
        (the surviving staircase carries exactly the pentagonal coefficient `(−1)ᵏ`,
         proved via `(-1)^{k.natAbs} = pentSign k` — the sign identity `neg_one_pow_natAbs`).

  We also prove the SUM-PRESERVATION of Franklin's two elementary moves as pure
  `Multiset` lemmas (`franklin_sum_invariant_down/up`): removing the smallest part
  and lengthening the top diagonal (remove two values `a`,`b`, add `a+b`), and its
  reverse (remove `a`, add `b`,`c` with `b+c=a`), BOTH preserve the partitioned
  integer `m`. These are exactly why Franklin's map lands back inside `Nat.Partition m`.

  We then package the still-missing ingredient (F1) as `FranklinMap m` — the
  involution on `distincts m \ fixedPart m` with its four properties FOR THE
  CONSTRUCTED FIXED SET — and prove `franklinData_of_franklinMap`: an `m`-level
  `FranklinMap` yields a full `FranklinData m` (reusing the proved F2 fields).
  Hence `∀ m, FranklinMap m` ⟹ the UNCONDITIONAL pentagonal number theorem
  (`pentagonalNumberTheorem_of_franklinMap`).

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `gauss_int`                  — `2·∑_{i<c} i = c(c−1)` over ℤ (division-free Gauss sum).
  * `stairBase`, `stair`         — the Franklin staircase multiset at integer index `k`.
  * `stair_card`                 — `|stair k| = k.natAbs` (the staircase has `|k|` parts).
  * `stair_nodup`                — the staircase parts are distinct.
  * `stair_pos`                  — every staircase part is positive.
  * `stair_sum`                  — **`(stair k).sum = pentagonal k`**: the staircase sums to
                                   the generalized pentagonal number `g_k` (the F2 arithmetic).
  * `stairPartAt`                — the staircase as an honest `Nat.Partition m` (when
                                   `pentagonal k = m`).
  * `neg_one_pow_natAbs`         — `(-1)^{k.natAbs} = pentSign k`: the staircase's sign is `(−1)ᵏ`.
  * `fixedPart`                  — Franklin's fixed set at `m` (the realizing staircase, or `∅`).
  * `fixedPart_subset`           — **F2, part 1:** the fixed set consists of distinct partitions.
  * `fixedPart_sum`              — **F2, part 2:** `∑_{fixedPart m} signOf = pentCoeff m`.
  * `franklin_sum_invariant_down/up`
                                 — **F1 arithmetic:** Franklin's two elementary moves preserve
                                   the partitioned integer (sum-preservation), so the map stays
                                   inside `Nat.Partition m`.
  * `FranklinMap`                — the isolated remaining ingredient (F1): the sign-reversing
                                   involution on `distincts m \ fixedPart m`.
  * `franklinData_of_franklinMap`— **the reduction:** a `FranklinMap m` completes the proved F2
                                   fields into a full `FranklinData m`.
  * `pentagonalNumberTheorem_of_franklinMap`
                                 — `∀ m, FranklinMap m` ⟹ the pentagonal number theorem
                                   (coefficient of Euler's product = `pentCoeff n`), UNCONDITIONALLY.

  ## What is NOT proved  (the residual obstruction, now down to F1 alone)
  * `∀ m, FranklinMap m` — the CONSTRUCTION of Franklin's sign-reversing involution `φ` on the
    non-fixed distinct partitions. The two staircase fixed points (F2) and the sum-preservation
    of the elementary moves (F1 arithmetic) are now proved; what remains is to define `φ` by the
    case split `sPart p ≤ tDiag p` vs `sPart p > tDiag p` (using the moves above), and to prove
    it MAPS non-fixed → non-fixed (`map_mem`, including that its only fixed points are the F2
    staircases), FLIPS the sign (`map_sign`), has NO fixed point off `fixedPart m` (`map_ne`),
    and is INVOLUTIVE (`map_involutive`). We do NOT assert `franklinData_exists`
    (`∀ m, FranklinData m`); we require `∀ m, FranklinMap m`.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  A term of `∀ m, FranklinMap m`. Everything about the FIXED points is proved: the staircases
  are constructed, shown distinct, positive, summing to `g_k`, and carrying signed count
  `pentCoeff m` (`fixedPart_sum`); and the elementary moves are shown sum-preserving. What is
  missing is the *global well-definedness and involutivity* of the map `φ`: that the
  `Multiset`-surgery moves preserve `Nodup` (distinctness) in every non-fixed case, that the
  case split is exhaustive off the two staircases, and that `φ ∘ φ = id`. This is the
  `Nodup`/case-analysis core of Franklin's bijection, still absent from Mathlib 4.32 and a
  development beyond one module. It is a single object: the involution `φ`.
-/
import Mathlib
import Brockian.PentagonalPartition
import Brockian.PentagonalTheoremFranklin
import Brockian.FranklinInvolution

set_option autoImplicit false

namespace Brockian.FranklinInvolutionProof

open Nat.Partition Finset
open Brockian.FranklinInvolution
open Brockian.PentagonalTheoremFranklin

/-! ### A division-free Gauss sum -/

/-- `2 · ∑_{i<c} i = c(c−1)` over ℤ, proved by induction (no natural-number subtraction, so it
casts cleanly into the pentagonal identity below). -/
theorem gauss_int (c : ℕ) : 2 * (∑ i ∈ Finset.range c, (i : ℤ)) = (c : ℤ) * ((c : ℤ) - 1) := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-! ### Franklin's fixed-point staircase -/

/-- The smallest part of the Franklin staircase at index `k`: `k` itself when `k > 0`, and
`|k|+1` when `k ≤ 0` (so `k = 0` gives an empty staircase and `k < 0` starts one higher). -/
def stairBase (k : ℤ) : ℕ := if 0 < k then k.natAbs else k.natAbs + 1

/-- Franklin's fixed-point staircase at integer index `k`: the multiset of `k.natAbs` consecutive
parts starting at `stairBase k`. For `k > 0` this is `{k, …, 2k−1}`; for `k < 0`, `{−k+1, …, −2k}`;
for `k = 0`, empty. This is the parts multiset of the pentagonal fixed point of Franklin's map. -/
def stair (k : ℤ) : Multiset ℕ := (Multiset.range k.natAbs).map (fun i => stairBase k + i)

/-- The staircase has exactly `|k|` parts. -/
theorem stair_card (k : ℤ) : Multiset.card (stair k) = k.natAbs := by
  rw [stair, Multiset.card_map, Multiset.card_range]

/-- The staircase parts are pairwise distinct. -/
theorem stair_nodup (k : ℤ) : (stair k).Nodup := by
  rw [stair]
  exact (Multiset.nodup_range k.natAbs).map (fun a b h => by omega)

/-- Every staircase part is positive. -/
theorem stair_pos {k : ℤ} {x : ℕ} (hx : x ∈ stair k) : 0 < x := by
  rw [stair, Multiset.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Multiset.mem_range] at hi
  have hk : k ≠ 0 := by rintro rfl; simp at hi
  have hb : 1 ≤ stairBase k := by unfold stairBase; split <;> omega
  omega

/-- The staircase written as an explicit `Finset.range` sum (for the sum computation). -/
theorem stair_sum_eq (k : ℤ) :
    (stair k).sum = ∑ i ∈ Finset.range k.natAbs, (stairBase k + i) := rfl

/-- **The F2 arithmetic heart.** The Franklin staircase at index `k` sums to the generalized
pentagonal number `g_k = k(3k−1)/2 = pentagonal k`. This is why the fixed points sit exactly at
the pentagonal exponents. -/
theorem stair_sum (k : ℤ) : (stair k).sum = pentagonal k := by
  -- Closed form of the staircase sum in ℕ (base·count + Gauss triangle), no cast ambiguity.
  have hnat : (stair k).sum = k.natAbs * stairBase k + ∑ i ∈ Finset.range k.natAbs, i := by
    rw [stair_sum_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- The doubled sum equals k(3k−1) over ℤ, by casework on the sign of k.
  have h2 : 2 * ((stair k).sum : ℤ) = k * (3 * k - 1) := by
    rw [hnat, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, mul_add, gauss_int]
    rcases lt_trichotomy k 0 with hk | hk | hk
    · -- k < 0
      have hc : (k.natAbs : ℤ) = -k := by rw [Int.natCast_natAbs, abs_of_neg hk]
      have hb : (stairBase k : ℤ) = -k + 1 := by
        rw [stairBase, if_neg (by omega), Nat.cast_add, Nat.cast_one, hc]
      rw [hc, hb]; ring
    · -- k = 0
      subst hk; simp [stairBase]
    · -- k > 0
      have hc : (k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_pos hk]
      have hb : (stairBase k : ℤ) = k := by rw [stairBase, if_pos hk]; exact hc
      rw [hc, hb]; ring
  have h2' : 2 * ((stair k).sum : ℤ) = 2 * (pentagonal k : ℤ) := by
    rw [h2, two_mul_natCast_pentagonal]
  have h3 := mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2'
  exact_mod_cast h3

/-- The Franklin staircase realized as an honest partition of `m`, when `pentagonal k = m`. -/
def stairPartAt (m : ℕ) (k : ℤ) (hk : pentagonal k = m) : m.Partition where
  parts := stair k
  parts_pos := fun {_} hi => stair_pos hi
  parts_sum := by rw [stair_sum]; exact hk

/-- The staircase's Franklin sign is `(−1)ᵏ`: `(-1)^{k.natAbs} = pentSign k`. This matches the
right-hand-side pentagonal coefficient. -/
theorem neg_one_pow_natAbs (k : ℤ) : (-1 : ℤ) ^ k.natAbs = pentSign k := by
  unfold pentSign
  rcases Int.even_or_odd k with he | ho
  · rw [if_pos he, Even.neg_one_pow (Int.natAbs_even.mpr he)]
  · rw [if_neg (Int.not_even_iff_odd.mpr ho), Odd.neg_one_pow (Int.natAbs_odd.mpr ho)]

/-! ### Franklin's fixed set (F2) -/

open Classical in
/-- Franklin's fixed set at `m`: the single realizing staircase when `m` is a generalized
pentagonal number, and `∅` otherwise. These are the partitions Franklin's involution fixes. -/
noncomputable def fixedPart (m : ℕ) : Finset m.Partition :=
  if h : ∃ k : ℤ, pentagonal k = m then {stairPartAt m h.choose h.choose_spec} else ∅

/-- **F2, part 1.** The fixed set consists of distinct partitions: `fixedPart m ⊆ distincts m`. -/
theorem fixedPart_subset (m : ℕ) : fixedPart m ⊆ distincts m := by
  by_cases hh : ∃ k : ℤ, pentagonal k = m
  · simp only [fixedPart, dif_pos hh]
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    simp only [distincts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact stair_nodup _
  · simp only [fixedPart, dif_neg hh]
    intro p hp
    simp at hp

/-- **F2, part 2.** The surviving fixed points carry exactly the pentagonal signed count:
`∑_{fixedPart m} signOf = pentCoeff m`. -/
theorem fixedPart_sum (m : ℕ) : ∑ p ∈ fixedPart m, signOf p = pentCoeff m := by
  by_cases hh : ∃ k : ℤ, pentagonal k = m
  · simp only [fixedPart, pentCoeff, dif_pos hh]
    rw [Finset.sum_singleton]
    show (-1 : ℤ) ^ (Multiset.card (stair hh.choose)) = pentSign hh.choose
    rw [stair_card]
    exact neg_one_pow_natAbs hh.choose
  · simp only [fixedPart, pentCoeff, dif_neg hh, Finset.sum_empty]

/-! ### Sum-preservation of Franklin's elementary moves (F1 arithmetic) -/

/-- **Down move preserves the sum.** Removing two parts `a`, `b` and adding one part `c = a+b`
(Franklin's "delete the smallest part, lengthen the top diagonal") keeps the partitioned integer
fixed. This is why the down-map lands back in `Nat.Partition m`. -/
theorem franklin_sum_invariant_down (s : Multiset ℕ) {a b c : ℕ}
    (ha : a ∈ s) (hb : b ∈ s.erase a) (habc : a + b = c) :
    (((s.erase a).erase b) + {c}).sum = s.sum := by
  have h1 : (s.erase a).sum + a = s.sum := by
    conv_rhs => rw [← Multiset.cons_erase ha]
    rw [Multiset.sum_cons]; omega
  have h2 : ((s.erase a).erase b).sum + b = (s.erase a).sum := by
    conv_rhs => rw [← Multiset.cons_erase hb]
    rw [Multiset.sum_cons]; omega
  rw [Multiset.sum_add, Multiset.sum_singleton]
  omega

/-- **Up move preserves the sum.** Removing one part `a` and adding two parts `b`, `c` with
`b + c = a` (Franklin's "peel the top diagonal into a new smallest part") keeps the partitioned
integer fixed. This is why the up-map lands back in `Nat.Partition m`. -/
theorem franklin_sum_invariant_up (s : Multiset ℕ) {a b c : ℕ}
    (ha : a ∈ s) (habc : b + c = a) :
    ((s.erase a) + (b ::ₘ {c})).sum = s.sum := by
  have h1 : (s.erase a).sum + a = s.sum := by
    conv_rhs => rw [← Multiset.cons_erase ha]
    rw [Multiset.sum_cons]; omega
  rw [Multiset.sum_add, Multiset.sum_cons, Multiset.sum_singleton]
  omega

/-! ### The isolated remaining ingredient (F1), and PST modulo it -/

/-- **The single residual object: Franklin's involution (F1), for the constructed fixed set.**
A term of `FranklinMap m` is exactly the sign-reversing involution on the non-fixed distinct
partitions `distincts m \ fixedPart m` — the one piece `FranklinData` still needs once the fixed
set (F2) is proved. -/
structure FranklinMap (m : ℕ) where
  /-- Franklin's map on the non-fixed distinct partitions. -/
  map : ∀ p ∈ distincts m \ fixedPart m, m.Partition
  /-- The map stays among non-fixed distinct partitions. -/
  map_mem : ∀ p (hp : p ∈ distincts m \ fixedPart m), map p hp ∈ distincts m \ fixedPart m
  /-- The map flips the sign (parity of the number of parts). -/
  map_sign : ∀ p (hp : p ∈ distincts m \ fixedPart m), signOf (map p hp) = - signOf p
  /-- The map has no fixed point off `fixedPart m`. -/
  map_ne : ∀ p (hp : p ∈ distincts m \ fixedPart m), map p hp ≠ p
  /-- The map is an involution. -/
  map_involutive : ∀ p (hp : p ∈ distincts m \ fixedPart m), map (map p hp) (map_mem p hp) = p

/-- **The reduction.** A Franklin involution (F1) at level `m` completes the proved fixed-set
fields (F2) into a full `FranklinData m`. Everything except `hm` — i.e. the whole fixed set and
its signed-count identity — is discharged here. -/
noncomputable def franklinData_of_franklinMap (m : ℕ) (hm : FranklinMap m) : FranklinData m where
  fixed := fixedPart m
  fixed_subset := fixedPart_subset m
  map := hm.map
  map_mem := hm.map_mem
  map_sign := hm.map_sign
  map_ne := hm.map_ne
  map_involutive := hm.map_involutive
  fixed_sum := fixedPart_sum m

/-- **The pentagonal number theorem, conditional only on the involution (F1).** Given Franklin's
involution at every level `m`, the `n`-th coefficient of Euler's product `genFun pstChar` equals
`pentCoeff n`. The cancellation engine and the whole fixed-point side (F2) are proved; the sole
hypothesis is the existence of the sign-reversing involution `∀ m, FranklinMap m`. We do NOT prove
that hypothesis, so this is a strict reduction of `franklinData_exists`, not the unconditional PST. -/
theorem pentagonalNumberTheorem_of_franklinMap (h : ∀ m, FranklinMap m) (n : ℕ) :
    (genFun pstChar).coeff n = pentCoeff n :=
  pentagonalNumberTheorem_of_franklinData (fun m => franklinData_of_franklinMap m (h m)) n

end Brockian.FranklinInvolutionProof
