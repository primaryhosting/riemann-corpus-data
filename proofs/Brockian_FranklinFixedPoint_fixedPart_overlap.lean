/-
  Brockian/FranklinFixedPoint.lean — CLOSING FRANKLIN'S INVOLUTION and proving the
  UNCONDITIONAL pentagonal number theorem (Aug 2).

  `Brockian/FranklinMapConstruction.lean` reduced `∀ m, FranklinMap m` — the last
  residual of the pentagonal number theorem — to FOUR named glue hypotheses of
  `franklinMap_of`:

    * `hd` / `hu`   — the FIXED-POINT CLASSIFICATION (off `fixedPart m` the two
                      non-overlap inequalities `2·sPart ≠ largest+1` and
                      `largest ≠ 2·tDiag` hold);
    * `hnotfixed`   — FIXED-SET STABILITY (`phi p ∉ fixedPart m`);
    * `hinv`        — GLOBAL INVOLUTIVITY (`phi (phi p) = p`).

  All four were blocked by the SAME source: `fixedPart m` is defined via
  `Exists.choose` on the pentagonal index, so it is OPAQUE — one could not decide
  `p ∈ fixedPart m` from the shape statistics. THIS MODULE DISCHARGES ALL FOUR and
  assembles the unconditional theorem.

  The keystone is the FIXED-POINT CLASSIFICATION

      `fixedPart_mem_iff : p ∈ fixedPart m ↔ ∃ k, pentagonal k = m ∧ p.parts = stair k`,

  proved by unfolding the `dif` and cancelling the `Exists.choose` against
  `pentagonal`'s injectivity (Mathlib's `pentagonal_injective`). From it:

    * `hd`, `hu` (`hd_of_mem`, `hu_of_mem`) — via `downOverlap_stair` / `upOverlap_stair`:
      on a distinct partition either overlap equality forces the parts multiset to BE a
      pentagonal staircase `stair k` (the top-diagonal run then covers `[sPart, largest]`),
      whence `pentagonal k = parts.sum = m`, so `p ∈ fixedPart m` — contradiction.
    * `hnotfixed` (`phi_notFixed`) — we compute the IMAGE statistics of the concrete moves
      (`downPart_largest/tDiag/sPart_gt`, `upPart_sPart/largest/le_branch`) and show the
      image satisfies NEITHER overlap, while `fixedPart_overlap` (staircase ⟹ overlap, from
      the staircase statistics `sPart/largestPart/tDiag_of_stair_pos/neg`) says every fixed
      point satisfies one. So the image is never fixed.
    * `hinv` (`phi_phi_eq`) — the multiset algebra `upMs (downPart p) = p.parts` and
      `downMs (upPart p) = p.parts`: the opposite move, whose parameters are pinned by the
      image statistics, undoes each elementary move.

  `hnz` (`parts_ne_zero_of_mem`) is proved via the classification (the empty partition is
  the `k = 0` staircase, hence fixed). These five facts feed `franklinMap_of`, giving
  `franklinMap_exists : ∀ m, FranklinMap m`, and via
  `Brockian.FranklinInvolutionProof.pentagonalNumberTheorem_of_franklinMap` the

      `pentagonalNumberTheorem : (genFun pstChar).coeff n = pentCoeff n`   (NO hypotheses).

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `stair_mem_iff`, `mem_stair_natCast`, `mem_stair_neg_natCast`
                                 — staircase membership as an explicit interval condition.
  * `fixedPart_mem_iff`          — **THE CLASSIFICATION.** De-opaques `Exists.choose`.
  * `parts_ne_zero_of_mem`       — `hnz`.
  * `downOverlap_stair`, `upOverlap_stair` — overlap ⟹ staircase.
  * `hd_of_mem`, `hu_of_mem`     — `hd`, `hu`.
  * `largestPart_eq_of`, `sPart_eq_of` — maximal/minimal part characterisations.
  * `sPart/largestPart/tDiag_of_stair_pos`/`_neg`, `fixedPart_overlap`
                                 — staircase statistics ⟹ every fixed point overlaps.
  * `down_L_ge`, `downPart_largest`, `downPart_tDiag`, `downPart_sPart_gt`, `upMs_downPart`
                                 — down-move image statistics + down∘up recovery.
  * `up_L_gt`, `upPart_sPart`, `upPart_largest`, `upPart_le_branch`, `downMs_upPart`
                                 — up-move image statistics + up∘down recovery.
  * `phi_notFixed`               — `hnotfixed`.
  * `phi_parts`, `phi_phi_eq`    — `hinv` (global involutivity).
  * `franklinMap_exists`         — **`∀ m, FranklinMap m`.** All four residuals discharged.
  * `pentagonalNumberTheorem`    — **THE UNCONDITIONAL PENTAGONAL NUMBER THEOREM**:
                                   `(genFun pstChar).coeff n = pentCoeff n`, no hypotheses.

  ## What is NOT proved
  Nothing is left open in this chain: the five `franklinMap_of` obligations are all closed,
  `franklinMap_exists` is a term (not an axiom), and `pentagonalNumberTheorem` is stated with
  no hypotheses. There is no `sorry`, `admit`, `native_decide`, or new `axiom` anywhere.
-/
import Mathlib
import Brockian.PentagonalPartition
import Brockian.PentagonalTheoremFranklin
import Brockian.FranklinInvolution
import Brockian.FranklinInvolutionProof
import Brockian.FranklinMapConstruction

set_option autoImplicit false

namespace Brockian.FranklinFixedPoint

open Nat.Partition Finset
open Brockian.FranklinInvolution
open Brockian.FranklinInvolutionProof
open Brockian.FranklinMapConstruction
open Brockian.PentagonalTheoremFranklin

variable {m : ℕ}

/-! ### Membership in the Franklin staircase -/

/-- Membership in the staircase `stair k` is an explicit interval condition: `a` lies in
`stair k` exactly when `stairBase k ≤ a < stairBase k + |k|`. -/
theorem stair_mem_iff (k : ℤ) (a : ℕ) :
    a ∈ stair k ↔ stairBase k ≤ a ∧ a < stairBase k + k.natAbs := by
  unfold stair
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Multiset.mem_range] at hi
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨a - stairBase k, Multiset.mem_range.mpr (by omega), by omega⟩

/-- For a positive index `t`, `stair (t : ℤ)` is the interval `[t, 2t − 1]`. -/
theorem mem_stair_natCast {t : ℕ} (ht : 1 ≤ t) (a : ℕ) :
    a ∈ stair (t : ℤ) ↔ t ≤ a ∧ a < 2 * t := by
  rw [stair_mem_iff]
  have hpos : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  have hb : stairBase (t : ℤ) = t := by
    unfold stairBase; rw [if_pos hpos]; exact Int.natAbs_natCast t
  have hn : ((t : ℤ)).natAbs = t := Int.natAbs_natCast t
  rw [hb, hn]; omega

/-- For a negative index `−t`, `stair (−t : ℤ)` is the interval `[t + 1, 2t]`. -/
theorem mem_stair_neg_natCast {t : ℕ} (ht : 1 ≤ t) (a : ℕ) :
    a ∈ stair (-(t : ℤ)) ↔ t + 1 ≤ a ∧ a < 2 * t + 1 := by
  rw [stair_mem_iff]
  have hpos : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
  have hb : stairBase (-(t : ℤ)) = t + 1 := by
    unfold stairBase; rw [if_neg (by omega)]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
  have hn : (-(t : ℤ)).natAbs = t := by rw [Int.natAbs_neg, Int.natAbs_natCast]
  rw [hb, hn]; omega

/-! ### The fixed-point classification (de-opaquing `fixedPart`) -/

/-- **The fixed-point classification.** `p ∈ fixedPart m` exactly when `p.parts` is the
Franklin staircase `stair k` at some index `k` with `pentagonal k = m`. This DE-OPAQUES the
`Exists.choose` in `fixedPart`: the `choose`-produced index is pinned down by `pentagonal`'s
injectivity, so membership is decidable from the parts multiset. -/
theorem fixedPart_mem_iff (m : ℕ) (p : m.Partition) :
    p ∈ fixedPart m ↔ ∃ k : ℤ, pentagonal k = m ∧ p.parts = stair k := by
  unfold fixedPart
  by_cases hh : ∃ k : ℤ, pentagonal k = m
  · rw [dif_pos hh, Finset.mem_singleton]
    constructor
    · intro hp
      exact ⟨hh.choose, hh.choose_spec, congrArg Nat.Partition.parts hp⟩
    · rintro ⟨k, hk, hps⟩
      apply Nat.Partition.ext
      show p.parts = stair hh.choose
      rw [hps]
      congr 1
      apply pentagonal_injective
      rw [hk, hh.choose_spec]
  · rw [dif_neg hh]
    constructor
    · intro hp; exact absurd hp (Finset.notMem_empty p)
    · rintro ⟨k, hk, _⟩; exact absurd ⟨k, hk⟩ hh

/-- `hnz`: a distinct partition off `fixedPart m` has nonempty parts. (The empty partition
sums to `0`, is the `k = 0` staircase `stair 0 = 0`, and thus lies in `fixedPart 0`.) -/
theorem parts_ne_zero_of_mem {p : m.Partition} (hp : p ∈ distincts m \ fixedPart m) :
    p.parts ≠ 0 := by
  intro h0
  have hnf : p ∉ fixedPart m := (Finset.mem_sdiff.mp hp).2
  apply hnf
  rw [fixedPart_mem_iff]
  have hsum : (0 : ℕ) = m := by
    have hps := p.parts_sum; rwa [h0, Multiset.sum_zero] at hps
  have hstair0 : stair (0 : ℤ) = 0 := by simp [stair]
  refine ⟨0, ?_, ?_⟩
  · have hst := stair_sum (0 : ℤ)
    rw [hstair0, Multiset.sum_zero] at hst
    rw [← hsum]; exact hst.symm
  · rw [h0, hstair0]

/-! ### Overlap ⟹ staircase, and the two non-overlap residuals -/

/-- **Down case, overlap ⟹ staircase.** If `p` is distinct and nonempty, `sPart p ≤ tDiag p`,
and the down-overlap `2·sPart p = largestPart p + 1` holds, then `p.parts = stair (sPart p)`:
the top diagonal covers the whole interval `[sPart p, largestPart p]`. -/
theorem downOverlap_stair {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p = largestPart p + 1) :
    p.parts = stair (tDiag p : ℤ) := by
  have hsp : 0 < sPart p := sPart_pos hnz
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  have hrun : largestPart p - (tDiag p - 1) ∈ p.parts := mem_of_lt_tDiag p (by omega)
  have hle : sPart p ≤ largestPart p - (tDiag p - 1) := sPart_le hnz hrun
  have hstt : sPart p = tDiag p := by omega
  have hL : largestPart p = 2 * tDiag p - 1 := by omega
  refine (Multiset.Nodup.ext hnd (stair_nodup _)).mpr (fun a => ?_)
  rw [mem_stair_natCast htp]
  constructor
  · intro ha
    have h1 : sPart p ≤ a := sPart_le hnz ha
    have h2 : a ≤ largestPart p := le_largestPart hnz ha
    omega
  · rintro ⟨hta, ha2⟩
    have hi : largestPart p - a < tDiag p := by omega
    have hmem := mem_of_lt_tDiag p hi
    have heq : largestPart p - (largestPart p - a) = a := by omega
    rwa [heq] at hmem

/-- **Up case, overlap ⟹ staircase.** If `p` is distinct and nonempty, `tDiag p < sPart p`,
and the up-overlap `largestPart p = 2·tDiag p` holds, then `p.parts = stair (−tDiag p)`. -/
theorem upOverlap_stair {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p = 2 * tDiag p) :
    p.parts = stair (-(tDiag p : ℤ)) := by
  have hsp : 0 < sPart p := sPart_pos hnz
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  have hrun : largestPart p - (tDiag p - 1) ∈ p.parts := mem_of_lt_tDiag p (by omega)
  have hle : sPart p ≤ largestPart p - (tDiag p - 1) := sPart_le hnz hrun
  have hstt : sPart p = tDiag p + 1 := by omega
  refine (Multiset.Nodup.ext hnd (stair_nodup _)).mpr (fun a => ?_)
  rw [mem_stair_neg_natCast htp]
  constructor
  · intro ha
    have h1 : sPart p ≤ a := sPart_le hnz ha
    have h2 : a ≤ largestPart p := le_largestPart hnz ha
    omega
  · rintro ⟨hta, ha2⟩
    have hi : largestPart p - a < tDiag p := by omega
    have hmem := mem_of_lt_tDiag p hi
    have heq : largestPart p - (largestPart p - a) = a := by omega
    rwa [heq] at hmem

/-- **`hd`.** Off `fixedPart m`, in the down case the down-overlap fails: `2·sPart ≠ largest+1`.
(If it held, `downOverlap_stair` makes `p` a staircase, hence `p ∈ fixedPart m`.) -/
theorem hd_of_mem {p : m.Partition} (hp : p ∈ distincts m \ fixedPart m) :
    sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1 := by
  intro hst hov
  have hnd : p.parts.Nodup := nodup_of_sdiff hp
  have hnf : p ∉ fixedPart m := (Finset.mem_sdiff.mp hp).2
  have hnz : p.parts ≠ 0 := parts_ne_zero_of_mem hp
  have hpe : p.parts = stair (tDiag p : ℤ) := downOverlap_stair hnz hnd hst hov
  apply hnf
  rw [fixedPart_mem_iff]
  refine ⟨(tDiag p : ℤ), ?_, hpe⟩
  have hs := stair_sum (tDiag p : ℤ)
  rw [← hpe, p.parts_sum] at hs
  exact hs.symm

/-- **`hu`.** Off `fixedPart m`, in the up case the up-overlap fails: `largest ≠ 2·tDiag`.
(If it held, `upOverlap_stair` makes `p` a staircase, hence `p ∈ fixedPart m`.) -/
theorem hu_of_mem {p : m.Partition} (hp : p ∈ distincts m \ fixedPart m) :
    tDiag p < sPart p → largestPart p ≠ 2 * tDiag p := by
  intro hst hov
  have hnd : p.parts.Nodup := nodup_of_sdiff hp
  have hnf : p ∉ fixedPart m := (Finset.mem_sdiff.mp hp).2
  have hnz : p.parts ≠ 0 := parts_ne_zero_of_mem hp
  have hpe : p.parts = stair (-(tDiag p : ℤ)) := upOverlap_stair hnz hnd hst hov
  apply hnf
  rw [fixedPart_mem_iff]
  refine ⟨-(tDiag p : ℤ), ?_, hpe⟩
  have hs := stair_sum (-(tDiag p : ℤ))
  rw [← hpe, p.parts_sum] at hs
  exact hs.symm

/-! ### Uniqueness characterisations of the shape statistics -/

/-- If `a` is a part and is maximal, it is the largest part. -/
theorem largestPart_eq_of {q : m.Partition} {a : ℕ} (ha : a ∈ q.parts)
    (hmax : ∀ x ∈ q.parts, x ≤ a) : largestPart q = a := by
  have hqnz : q.parts ≠ 0 := by intro h; rw [h] at ha; exact Multiset.notMem_zero a ha
  exact le_antisymm (hmax _ (largestPart_mem hqnz)) (le_largestPart hqnz ha)

/-- If `a` is a part and is minimal, it is the smallest part. -/
theorem sPart_eq_of {q : m.Partition} {a : ℕ} (ha : a ∈ q.parts)
    (hmin : ∀ x ∈ q.parts, a ≤ x) : sPart q = a := by
  have hqnz : q.parts ≠ 0 := by intro h; rw [h] at ha; exact Multiset.notMem_zero a ha
  exact le_antisymm (sPart_le hqnz ha) (hmin _ (sPart_mem hqnz))

/-! ### Shape statistics of the staircase (staircase ⟹ overlap) -/

theorem sPart_of_stair_pos {q : m.Partition} {t : ℕ} (ht : 1 ≤ t)
    (hq : q.parts = stair (t : ℤ)) : sPart q = t := by
  apply sPart_eq_of
  · rw [hq, mem_stair_natCast ht]; omega
  · intro x hx; rw [hq, mem_stair_natCast ht] at hx; omega

theorem largestPart_of_stair_pos {q : m.Partition} {t : ℕ} (ht : 1 ≤ t)
    (hq : q.parts = stair (t : ℤ)) : largestPart q = 2 * t - 1 := by
  apply largestPart_eq_of
  · rw [hq, mem_stair_natCast ht]; omega
  · intro x hx; rw [hq, mem_stair_natCast ht] at hx; omega

theorem tDiag_of_stair_pos {q : m.Partition} {t : ℕ} (ht : 1 ≤ t)
    (hq : q.parts = stair (t : ℤ)) : tDiag q = t := by
  have hL : largestPart q = 2 * t - 1 := largestPart_of_stair_pos ht hq
  unfold tDiag
  rw [Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [hL, hq]; intro hc; rw [mem_stair_natCast ht] at hc; omega
  · intro n hn; rw [not_not, hL, hq, mem_stair_natCast ht]; omega

theorem sPart_of_stair_neg {q : m.Partition} {t : ℕ} (ht : 1 ≤ t)
    (hq : q.parts = stair (-(t : ℤ))) : sPart q = t + 1 := by
  apply sPart_eq_of
  · rw [hq, mem_stair_neg_natCast ht]; omega
  · intro x hx; rw [hq, mem_stair_neg_natCast ht] at hx; omega

theorem largestPart_of_stair_neg {q : m.Partition} {t : ℕ} (ht : 1 ≤ t)
    (hq : q.parts = stair (-(t : ℤ))) : largestPart q = 2 * t := by
  apply largestPart_eq_of
  · rw [hq, mem_stair_neg_natCast ht]; omega
  · intro x hx; rw [hq, mem_stair_neg_natCast ht] at hx; omega

theorem tDiag_of_stair_neg {q : m.Partition} {t : ℕ} (ht : 1 ≤ t)
    (hq : q.parts = stair (-(t : ℤ))) : tDiag q = t := by
  have hL : largestPart q = 2 * t := largestPart_of_stair_neg ht hq
  unfold tDiag
  rw [Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [hL, hq]; intro hc; rw [mem_stair_neg_natCast ht] at hc; omega
  · intro n hn; rw [not_not, hL, hq, mem_stair_neg_natCast ht]; omega

/-- **Fixed points satisfy an overlap.** A nonempty member of `fixedPart m` is a staircase, hence
its statistics satisfy one of the two overlap equalities. -/
theorem fixedPart_overlap {q : m.Partition} (hq : q ∈ fixedPart m) (hqnz : q.parts ≠ 0) :
    (sPart q ≤ tDiag q ∧ 2 * sPart q = largestPart q + 1) ∨
      (tDiag q < sPart q ∧ largestPart q = 2 * tDiag q) := by
  obtain ⟨k, _, hps⟩ := (fixedPart_mem_iff m q).mp hq
  have hstair0 : stair (0 : ℤ) = 0 := by simp [stair]
  have hk0 : k ≠ 0 := by rintro rfl; rw [hstair0] at hps; exact hqnz hps
  rcases lt_trichotomy k 0 with hneg | hz | hpos
  · have ht : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk0
    have hkt : -(k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_neg hneg]; ring
    rw [← hkt] at hps
    have hs := sPart_of_stair_neg ht hps
    have hL := largestPart_of_stair_neg ht hps
    have hT := tDiag_of_stair_neg ht hps
    right; rw [hs, hL, hT]; omega
  · exact absurd hz hk0
  · have ht : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk0
    have hkt : (k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_pos hpos]
    rw [← hkt] at hps
    have hs := sPart_of_stair_pos ht hps
    have hL := largestPart_of_stair_pos ht hps
    have hT := tDiag_of_stair_pos ht hps
    left; rw [hs, hL, hT]; omega

/-! ### Down-move image statistics -/

/-- In the down non-overlap case, `largestPart p ≥ 2·sPart p` (the top diagonal, length `≥ sPart`,
reaches down to `≥ sPart`, and non-overlap rules out equality). -/
theorem down_L_ge {p : m.Partition} (hnz : p.parts ≠ 0)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    2 * sPart p ≤ largestPart p := by
  have hsp : 0 < sPart p := sPart_pos hnz
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  have hrun : largestPart p - (tDiag p - 1) ∈ p.parts := mem_of_lt_tDiag p (by omega)
  have hle : sPart p ≤ largestPart p - (tDiag p - 1) := sPart_le hnz hrun
  omega

/-- The down move sets the largest part to `largestPart p + 1`. -/
theorem downPart_largest {p : m.Partition} (hnz : p.parts ≠ 0)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    largestPart (downPart p hnz hst hov) = largestPart p + 1 := by
  apply largestPart_eq_of
  · show largestPart p + 1 ∈ downMs p
    rw [downMs]; exact Multiset.mem_cons_self _ _
  · intro x hx
    have hx' : x ∈ downMs p := hx
    rw [downMs, Multiset.mem_cons] at hx'
    rcases hx' with h | h
    · omega
    · have hxp : x ∈ p.parts := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase h)
      have := le_largestPart hnz hxp
      omega

/-- The down move sets the top diagonal length to `sPart p`. -/
theorem downPart_tDiag {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    tDiag (downPart p hnz hst hov) = sPart p := by
  have hL2s := down_L_ge hnz hst hov
  have hsp : 0 < sPart p := sPart_pos hnz
  have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
  have hLarge := downPart_largest hnz hst hov
  unfold tDiag
  rw [Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [hLarge]
    intro hcontra
    have hc : largestPart p + 1 - sPart p ∈ downMs p := hcontra
    rw [show largestPart p + 1 - sPart p = largestPart p - sPart p + 1 from by omega] at hc
    rw [downMs, Multiset.mem_cons] at hc
    rcases hc with h | h
    · omega
    · exact (hnd.erase (sPart p)).notMem_erase h
  · intro i hi
    rw [not_not, hLarge]
    show largestPart p + 1 - i ∈ downMs p
    rw [downMs, Multiset.mem_cons]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · left; omega
    · right
      have hin : largestPart p - (i - 1) ∈ p.parts := mem_of_lt_tDiag p (by omega)
      rw [show largestPart p - (i - 1) = largestPart p + 1 - i from by omega] at hin
      have hne1 : largestPart p + 1 - i ≠ sPart p := by omega
      have hne2 : largestPart p + 1 - i ≠ largestPart p - sPart p + 1 := by omega
      exact (Multiset.mem_erase_of_ne hne2).mpr ((Multiset.mem_erase_of_ne hne1).mpr hin)

/-- The down move strictly raises the smallest part (the old minimum was deleted). -/
theorem downPart_sPart_gt {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    sPart p < sPart (downPart p hnz hst hov) := by
  have hdnz : (downPart p hnz hst hov).parts ≠ 0 := by
    show downMs p ≠ 0; rw [downMs]; exact Multiset.cons_ne_zero
  have hmem : sPart (downPart p hnz hst hov) ∈ (downPart p hnz hst hov).parts := sPart_mem hdnz
  have hmem' : sPart (downPart p hnz hst hov) ∈ downMs p := hmem
  rw [downMs, Multiset.mem_cons] at hmem'
  have hL2s := down_L_ge hnz hst hov
  have hsp : 0 < sPart p := sPart_pos hnz
  rcases hmem' with h | h
  · omega
  · have hin : sPart (downPart p hnz hst hov) ∈ p.parts.erase (sPart p) :=
      Multiset.mem_of_mem_erase h
    have hne : sPart (downPart p hnz hst hov) ≠ sPart p := fun he => hnd.notMem_erase (he ▸ hin)
    have hge : sPart p ≤ sPart (downPart p hnz hst hov) := sPart_le hnz (Multiset.mem_of_mem_erase hin)
    omega

/-- **Down-then-up recovers `p`.** The up move applied to the down image gives back `p.parts`. -/
theorem upMs_downPart {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    upMs (downPart p hnz hst hov) = p.parts := by
  have hLarge := downPart_largest hnz hst hov
  have hT := downPart_tDiag hnz hnd hst hov
  have hL2s := down_L_ge hnz hst hov
  have hsp : 0 < sPart p := sPart_pos hnz
  have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
  have hs_mem : sPart p ∈ p.parts := sPart_mem hnz
  have hd_memp : largestPart p - sPart p + 1 ∈ p.parts := d_mem hnz hst
  have hdne : largestPart p - sPart p + 1 ≠ sPart p := by omega
  have hd_in : largestPart p - sPart p + 1 ∈ p.parts.erase (sPart p) :=
    (Multiset.mem_erase_of_ne hdne).mpr hd_memp
  unfold upMs
  rw [hLarge, hT]
  have he1 : (downPart p hnz hst hov).parts.erase (largestPart p + 1)
      = (p.parts.erase (sPart p)).erase (largestPart p - sPart p + 1) := by
    show (downMs p).erase (largestPart p + 1) = _
    rw [downMs, Multiset.erase_cons_head]
  rw [he1, show largestPart p + 1 - sPart p = largestPart p - sPart p + 1 from by omega]
  rw [Multiset.cons_erase hd_in, Multiset.cons_erase hs_mem]

/-! ### Up-move image statistics -/

/-- In the up non-overlap case, `largestPart p > 2·tDiag p`. -/
theorem up_L_gt {p : m.Partition} (hnz : p.parts ≠ 0)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) :
    2 * tDiag p < largestPart p := by
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  have hrun : largestPart p - (tDiag p - 1) ∈ p.parts := mem_of_lt_tDiag p (by omega)
  have hle : sPart p ≤ largestPart p - (tDiag p - 1) := sPart_le hnz hrun
  omega

/-- The up move sets the smallest part to `tDiag p`. -/
theorem upPart_sPart {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) :
    sPart (upPart p hnz hst) = tDiag p := by
  have hLgt := up_L_gt hnz hst hov
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  apply sPart_eq_of
  · show tDiag p ∈ upMs p
    rw [upMs]; exact Multiset.mem_cons_self _ _
  · intro x hx
    have hx' : x ∈ upMs p := hx
    rw [upMs, Multiset.mem_cons, Multiset.mem_cons] at hx'
    rcases hx' with h | h | h
    · omega
    · omega
    · have hxp : x ∈ p.parts := Multiset.mem_of_mem_erase h
      have := sPart_le hnz hxp
      omega

/-- The up move sets the largest part to `largestPart p − 1`. -/
theorem upPart_largest {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) :
    largestPart (upPart p hnz hst) = largestPart p - 1 := by
  have hLgt := up_L_gt hnz hst hov
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  apply largestPart_eq_of
  · show largestPart p - 1 ∈ upMs p
    rw [upMs]
    by_cases ht1 : tDiag p = 1
    · apply Multiset.mem_cons_of_mem
      rw [show largestPart p - tDiag p = largestPart p - 1 from by omega]
      exact Multiset.mem_cons_self _ _
    · apply Multiset.mem_cons_of_mem
      apply Multiset.mem_cons_of_mem
      have hmem : largestPart p - 1 ∈ p.parts := mem_of_lt_tDiag p (by omega)
      exact (Multiset.mem_erase_of_ne (show largestPart p - 1 ≠ largestPart p from by omega)).mpr hmem
  · intro x hx
    have hx' : x ∈ upMs p := hx
    rw [upMs, Multiset.mem_cons, Multiset.mem_cons] at hx'
    rcases hx' with h | h | h
    · omega
    · omega
    · have hxp : x ∈ p.parts := Multiset.mem_of_mem_erase h
      have hxne : x ≠ largestPart p := fun he => hnd.notMem_erase (he ▸ h)
      have hxle := le_largestPart hnz hxp
      omega

/-- The up image is again in the down case: `sPart ≤ tDiag`. -/
theorem upPart_le_branch {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) :
    sPart (upPart p hnz hst) ≤ tDiag (upPart p hnz hst) := by
  have hSp := upPart_sPart hnz hnd hst hov
  have hLarge := upPart_largest hnz hnd hst hov
  have hLgt := up_L_gt hnz hst hov
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  have key : ∀ i < tDiag p, largestPart (upPart p hnz hst) - i ∈ (upPart p hnz hst).parts := by
    intro i hi
    rw [hLarge]
    show largestPart p - 1 - i ∈ upMs p
    rw [upMs]
    by_cases hie : i = tDiag p - 1
    · apply Multiset.mem_cons_of_mem
      rw [show largestPart p - 1 - i = largestPart p - tDiag p from by omega]
      exact Multiset.mem_cons_self _ _
    · apply Multiset.mem_cons_of_mem
      apply Multiset.mem_cons_of_mem
      have hmem : largestPart p - 1 - i ∈ p.parts := by
        have hd2 := mem_of_lt_tDiag p (show i + 1 < tDiag p from by omega)
        rwa [show largestPart p - (i + 1) = largestPart p - 1 - i from by omega] at hd2
      exact (Multiset.mem_erase_of_ne
        (show largestPart p - 1 - i ≠ largestPart p from by omega)).mpr hmem
  rw [hSp]
  by_contra hcon
  push_neg at hcon
  exact tDiag_notMem (upPart p hnz hst) (key (tDiag (upPart p hnz hst)) hcon)

/-- **Up-then-down recovers `p`.** The down move applied to the up image gives back `p.parts`. -/
theorem downMs_upPart {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) :
    downMs (upPart p hnz hst) = p.parts := by
  have hSp := upPart_sPart hnz hnd hst hov
  have hLarge := upPart_largest hnz hnd hst hov
  have hLgt := up_L_gt hnz hst hov
  have htp : 1 ≤ tDiag p := one_le_tDiag hnz
  have hL_mem : largestPart p ∈ p.parts := largestPart_mem hnz
  unfold downMs
  rw [hSp, hLarge]
  rw [show largestPart p - 1 + 1 = largestPart p from by omega,
      show largestPart p - 1 - tDiag p + 1 = largestPart p - tDiag p from by omega]
  have he1 : (upPart p hnz hst).parts.erase (tDiag p)
      = (largestPart p - tDiag p) ::ₘ (p.parts.erase (largestPart p)) := by
    show (upMs p).erase (tDiag p) = _
    rw [upMs, Multiset.erase_cons_head]
  rw [he1, Multiset.erase_cons_head, Multiset.cons_erase hL_mem]

/-! ### Fixed-set stability (`hnotfixed`) -/

/-- The down image is not a fixed point. -/
theorem downPart_notFixed {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    downPart p hnz hst hov ∉ fixedPart m := by
  intro hfix
  have hLarge := downPart_largest hnz hst hov
  have hT := downPart_tDiag hnz hnd hst hov
  have hSgt := downPart_sPart_gt hnz hnd hst hov
  have hdnz : (downPart p hnz hst hov).parts ≠ 0 := by
    show downMs p ≠ 0; rw [downMs]; exact Multiset.cons_ne_zero
  have hup : tDiag (downPart p hnz hst hov) < sPart (downPart p hnz hst hov) := by
    rw [hT]; exact hSgt
  rcases fixedPart_overlap hfix hdnz with ⟨hle, _⟩ | ⟨_, hov'⟩
  · omega
  · rw [hLarge, hT] at hov'; omega

/-- The up image is not a fixed point. -/
theorem upPart_notFixed {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) :
    upPart p hnz hst ∉ fixedPart m := by
  intro hfix
  have hSp := upPart_sPart hnz hnd hst hov
  have hLarge := upPart_largest hnz hnd hst hov
  have hbr := upPart_le_branch hnz hnd hst hov
  have hLgt := up_L_gt hnz hst hov
  have hunz : (upPart p hnz hst).parts ≠ 0 := by
    show upMs p ≠ 0; rw [upMs]; exact Multiset.cons_ne_zero
  rcases fixedPart_overlap hfix hunz with ⟨_, hov'⟩ | ⟨hlt, _⟩
  · rw [hSp, hLarge] at hov'; omega
  · omega

/-- **`hnotfixed`.** Franklin's map keeps a non-fixed distinct partition non-fixed. -/
theorem phi_notFixed {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hd : sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : tDiag p < sPart p → largestPart p ≠ 2 * tDiag p) :
    phi p hnz hd hu ∉ fixedPart m := by
  unfold phi
  split_ifs with h
  · exact downPart_notFixed hnz hnd h (hd h)
  · exact upPart_notFixed hnz hnd (not_le.mp h) (hu (not_le.mp h))

/-! ### Global involutivity (`hinv`) -/

/-- The parts of `phi q …` are `downMs q` or `upMs q` according to the case split — independent of
the proof arguments. -/
theorem phi_parts {q : m.Partition} (hq : q.parts ≠ 0)
    (bd : sPart q ≤ tDiag q → 2 * sPart q ≠ largestPart q + 1)
    (bu : tDiag q < sPart q → largestPart q ≠ 2 * tDiag q) :
    (phi q hq bd bu).parts = if sPart q ≤ tDiag q then downMs q else upMs q := by
  unfold phi; split_ifs <;> rfl

/-- **`hinv`.** Franklin's map is an involution: `phi (phi p …) … = p`, for any proof arguments. -/
theorem phi_phi_eq {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hd : sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : tDiag p < sPart p → largestPart p ≠ 2 * tDiag p)
    (hnz2 : (phi p hnz hd hu).parts ≠ 0)
    (hd2 : sPart (phi p hnz hd hu) ≤ tDiag (phi p hnz hd hu) →
      2 * sPart (phi p hnz hd hu) ≠ largestPart (phi p hnz hd hu) + 1)
    (hu2 : tDiag (phi p hnz hd hu) < sPart (phi p hnz hd hu) →
      largestPart (phi p hnz hd hu) ≠ 2 * tDiag (phi p hnz hd hu)) :
    phi (phi p hnz hd hu) hnz2 hd2 hu2 = p := by
  by_cases h : sPart p ≤ tDiag p
  · have hpe : phi p hnz hd hu = downPart p hnz h (hd h) := by unfold phi; rw [dif_pos h]
    apply Nat.Partition.ext
    rw [phi_parts, hpe]
    split_ifs with h'
    · exfalso
      have htd := downPart_tDiag hnz hnd h (hd h)
      have hgt := downPart_sPart_gt hnz hnd h (hd h)
      omega
    · exact upMs_downPart hnz hnd h (hd h)
  · have hlt : tDiag p < sPart p := not_le.mp h
    have hov : largestPart p ≠ 2 * tDiag p := hu hlt
    have hpe : phi p hnz hd hu = upPart p hnz hlt := by unfold phi; rw [dif_neg h]
    apply Nat.Partition.ext
    rw [phi_parts, hpe]
    split_ifs with h'
    · exact downMs_upPart hnz hnd hlt hov
    · exact absurd (upPart_le_branch hnz hnd hlt hov) h'

/-! ### Assembling `FranklinMap` and the unconditional pentagonal number theorem -/

/-- **Franklin's involution exists at every level.** All four residual hypotheses of
`franklinMap_of` are now discharged. -/
noncomputable def franklinMap_exists (m : ℕ) : FranklinMap m :=
  franklinMap_of m
    (fun _ hp => parts_ne_zero_of_mem hp)
    (fun _ hp => hd_of_mem hp)
    (fun _ hp => hu_of_mem hp)
    (fun _ hp => phi_notFixed (parts_ne_zero_of_mem hp) (nodup_of_sdiff hp)
      (hd_of_mem hp) (hu_of_mem hp))
    (fun _ hp => phi_phi_eq (parts_ne_zero_of_mem hp) (nodup_of_sdiff hp)
      (hd_of_mem hp) (hu_of_mem hp) _ _ _)

/-- **THE PENTAGONAL NUMBER THEOREM (unconditional).** The `n`-th coefficient of Euler's product
`genFun pstChar = ∏_{i≥1}(1 − xⁱ)` equals `pentCoeff n`, the coefficient of `∑_{k∈ℤ}(−1)ᵏ x^{g_k}`.
No hypotheses: Franklin's sign-reversing involution is fully constructed above. -/
theorem pentagonalNumberTheorem (n : ℕ) : (genFun pstChar).coeff n = pentCoeff n :=
  pentagonalNumberTheorem_of_franklinMap (fun m => franklinMap_exists m) n

end Brockian.FranklinFixedPoint
