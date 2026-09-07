/-
  Brockian/FranklinMapConstruction.lean — CONSTRUCTING FRANKLIN'S SIGN-REVERSING
  INVOLUTION φ as a concrete operation on `Nat.Partition`, and reducing the last
  residual `∀ m, FranklinMap m` of the pentagonal number theorem to a precisely
  named triple of glue lemmas (Aug 2).

  `Brockian/FranklinInvolutionProof.lean` had driven the entire pentagonal number
  theorem down to ONE object: a term of `∀ m, FranklinMap m`, the sign-reversing
  involution on the non-fixed distinct partitions `distincts m \ fixedPart m`.
  It already proved the fixed-point side (F2, the two pentagonal staircases and
  `fixedPart_sum = pentCoeff`) and the SUM-PRESERVATION of Franklin's two elementary
  moves (`franklin_sum_invariant_down/up`). What remained was the map itself.

  THIS MODULE CONSTRUCTS THE MAP CONCRETELY. The decisive simplification: on a
  DISTINCT partition (`Nodup` parts), Franklin's two moves are clean multiset
  surgeries whose sum-preservation is *exactly* the two invariants already proved.

  Writing `s = sPart p` (smallest part), `t = tDiag p` (top-diagonal length),
  `L = largestPart p` (largest part):

    * DOWN move (case `s ≤ t`) — "delete the smallest part, add 1 to the top `s`
      parts". As a distinct-partition surgery this is: remove `s`, remove `L−s+1`,
      insert `L+1`. (Adding 1 to the contiguous block `L, L−1, …, L−s+1` shifts it
      to `L+1, L, …, L−s+2`; only the bottom `L−s+1` leaves and the new top `L+1`
      enters, the middle is unchanged.) Encoded as `downMs`. Because
      `s + (L−s+1) = L+1`, its sum-preservation IS `franklin_sum_invariant_down`.

    * UP move (case `s > t`) — "peel 1 off the top `t` parts, create a new smallest
      part of size `t`". As a surgery: remove `L`, insert `L−t` and `t`. (Subtracting
      1 from the contiguous top block shifts it down; only `L` leaves and `L−t`
      enters; `t` is a brand-new smallest part.) Encoded as `upMs`. Because
      `t + (L−t) = L`, its sum-preservation IS `franklin_sum_invariant_up`.

  For each move we build the honest `Nat.Partition m` (`downPart`, `upPart`) — the
  positivity and sum obligations are DISCHARGED — and prove the two combinatorial
  invariants Mathlib was missing:

    * DISTINCTNESS (`Nodup`) is PRESERVED (`downMs_nodup`, `upMs_nodup`): the new
      top `L+1` is absent because it exceeds the maximum; the new bottom `L−t` is
      absent by `tDiag_notMem`; the new smallest `t` is absent because `t < s`; and
      the non-fixed hypotheses `2s ≠ L+1`, `L ≠ 2t` rule out the two staircase
      self-collisions.
    * The PART COUNT changes by exactly one (`downMs_card`, `upMs_card`), hence the
      SIGN FLIPS (`downPart_sign`, `upPart_sign`) and the map is NON-FIXED
      (`downPart_ne`, `upPart_ne`, `phi_ne`).

  These are combined into the concrete map `phi` (case split on `s ≤ t`), and its
  three field-level properties are proved: sign reversal (`phi_sign`), distinctness
  of the image (`phi_parts_nodup`), non-fixedness (`phi_ne`). We then package the
  reduction `franklinMap_of`: given the residual glue — the non-overlap
  classification (`hd`, `hu`), the fixed-set stability (`hnotfixed`), and
  involutivity (`hinv`) — a full `FranklinMap m` follows, with `map_sign`,
  `map_ne`, and the `Nodup` half of `map_mem` DISCHARGED here.

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `sPart_pos`, `sPart_le_largest`, `d_mem`
                                 — helper facts on the Franklin statistics: the
                                   smallest part is positive, `s ≤ L`, and the
                                   down-move target `L−s+1` is an actual part.
  * `downMs`, `upMs`             — Franklin's two moves as explicit `Multiset ℕ`
                                   surgeries.
  * `downPart`, `upPart`         — the two moves as honest `Nat.Partition m`
                                   (POSITIVITY and SUM discharged, reusing
                                   `franklin_sum_invariant_down/up`).
  * `downMs_nodup`, `upMs_nodup` — **distinctness is preserved** by both moves (the
                                   `Nodup`-surgery core Mathlib lacked).
  * `downMs_card`, `upMs_card`   — the part count changes by exactly one.
  * `downPart_sign`, `upPart_sign`
                                 — **the sign reverses**: `signOf (move p) = −signOf p`.
  * `downPart_ne`, `upPart_ne`   — the move has no fixed point (part count differs).
  * `phi`                        — Franklin's involution as ONE concrete map, by the
                                   classical case split `s ≤ t` vs `s > t`.
  * `phi_sign`                   — `signOf (phi p) = −signOf p`   (field `map_sign`).
  * `phi_parts_nodup`            — `(phi p).parts.Nodup`  (the `Nodup` half of `map_mem`).
  * `phi_ne`                     — `phi p ≠ p`             (field `map_ne`).
  * `nodup_of_sdiff`, `phiMem`   — image lands in `distincts m` (given fixed-set
                                   stability), assembling the `map_mem` field.
  * `franklinMap_of`             — **the reduction.** From the residual glue
                                   (`hd`,`hu`,`hnotfixed`,`hinv`) a full `FranklinMap m`,
                                   with three of the four fields discharged here.

  ## What is NOT proved  (the residual, now three named glue lemmas)
  * `∀ m, FranklinMap m` is NOT asserted. `franklinMap_of` still requires:
      - `hd`,`hu`  — the FIXED-POINT CLASSIFICATION: off `fixedPart m` the non-overlap
                     inequalities `2·sPart p ≠ largestPart p + 1` (down) and
                     `largestPart p ≠ 2·tDiag p` (up) hold. Equivalently: the only
                     self-collisions of the two moves are the pentagonal staircases.
      - `hnotfixed` — FIXED-SET STABILITY: `phi p ∉ fixedPart m` (the map keeps
                      non-fixed partitions non-fixed).
      - `hinv`      — GLOBAL INVOLUTIVITY: `phi (phi p) = p` (up∘down = down∘up = id
                      after recomputing `s,t,L` on the image).
    We do NOT provide these, so we do NOT provide `franklinMap_exists`. The map and
    three of its four field-properties (`map_sign`, `map_ne`, and `Nodup` of image)
    are proved unconditionally here.

  ## Precise remaining obstruction (exact missing Mathlib combinatorics)
  The construction of `φ` and its LOCAL properties (sum, positivity, distinctness,
  sign, non-fixedness) are now proved. Three GLOBAL facts remain, all obstructed by
  the same source — `fixedPart m` is defined via `Exists.choose` on the pentagonal
  index, so it is OPAQUE: one cannot yet decide `p ∈ fixedPart m` from the shape
  statistics `s,t,L`. Discharging the residual needs a FIXED-POINT CLASSIFICATION
  theorem `p ∈ fixedPart m ↔ (staircase-shape / overlap condition on s,t,L)`,
  from which `hd`,`hu`,`hnotfixed` follow, plus the algebraic INVOLUTIVITY
  `hinv` (recomputing the statistics of `downMs p` / `upMs p` and checking the
  opposite move inverts it). None of this is a `sorry` in any claimed-proved
  theorem here: the residual is exhibited as explicit hypotheses of `franklinMap_of`.
-/
import Mathlib
import Brockian.PentagonalPartition
import Brockian.PentagonalTheoremFranklin
import Brockian.FranklinInvolution
import Brockian.FranklinInvolutionProof

set_option autoImplicit false

namespace Brockian.FranklinMapConstruction

open Nat.Partition Finset
open Brockian.FranklinInvolution
open Brockian.FranklinInvolutionProof

variable {m : ℕ}

/-! ### Helper facts on the Franklin statistics -/

/-- The smallest part of a nonempty partition is positive. -/
theorem sPart_pos {p : m.Partition} (hnz : p.parts ≠ 0) : 0 < sPart p :=
  p.parts_pos (sPart_mem hnz)

/-- The smallest part is at most the largest part. -/
theorem sPart_le_largest {p : m.Partition} (hnz : p.parts ≠ 0) : sPart p ≤ largestPart p :=
  le_largestPart hnz (sPart_mem hnz)

/-- In the down case (`sPart p ≤ tDiag p`) the down-move target `L − s + 1` is an actual
part: it is the value `L − (s−1)`, inside the top diagonal. -/
theorem d_mem {p : m.Partition} (hnz : p.parts ≠ 0) (hst : sPart p ≤ tDiag p) :
    largestPart p - sPart p + 1 ∈ p.parts := by
  have hsp : 0 < sPart p := sPart_pos hnz
  have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
  have hlt : sPart p - 1 < tDiag p := by omega
  have hmem := mem_of_lt_tDiag p hlt
  have heq : largestPart p - (sPart p - 1) = largestPart p - sPart p + 1 := by omega
  rwa [heq] at hmem

/-! ### Franklin's two moves as multiset surgeries -/

/-- Franklin's DOWN move on the parts multiset (case `sPart p ≤ tDiag p`): remove the
smallest part `s` and the value `L − s + 1`, insert the new top `L + 1`. -/
noncomputable def downMs (p : m.Partition) : Multiset ℕ :=
  (largestPart p + 1) ::ₘ ((p.parts.erase (sPart p)).erase (largestPart p - sPart p + 1))

/-- Franklin's UP move on the parts multiset (case `sPart p > tDiag p`): remove the largest
part `L`, insert the new bottom `L − t` and the new smallest part `t`. -/
noncomputable def upMs (p : m.Partition) : Multiset ℕ :=
  tDiag p ::ₘ (largestPart p - tDiag p) ::ₘ (p.parts.erase (largestPart p))

/-! ### Distinctness is preserved -/

/-- The down move preserves `Nodup`: the inserted top `L+1` exceeds every part, and erasing
keeps distinctness. -/
theorem downMs_nodup {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup) :
    (downMs p).Nodup := by
  have hin : ((p.parts.erase (sPart p)).erase (largestPart p - sPart p + 1)).Nodup :=
    (hnd.erase (sPart p)).erase (largestPart p - sPart p + 1)
  have hL1 : largestPart p + 1 ∉ p.parts := fun hmem => by
    have := le_largestPart hnz hmem; omega
  refine Multiset.nodup_cons.mpr ⟨?_, hin⟩
  intro hmem
  exact hL1 (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hmem))

/-- The up move preserves `Nodup`: the new bottom `L−t` is absent by `tDiag_notMem`, the new
smallest `t` is absent because `t < s ≤` every part, and `L ≠ 2t` rules out `t = L−t`. -/
theorem upMs_nodup {p : m.Partition} (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hst : tDiag p < sPart p) (hov : largestPart p ≠ 2 * tDiag p) : (upMs p).Nodup := by
  have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
  have htL : tDiag p < largestPart p := by omega
  have h1 : (p.parts.erase (largestPart p)).Nodup := hnd.erase (largestPart p)
  have hlo_not : largestPart p - tDiag p ∉ p.parts := tDiag_notMem p
  have hlo_ne : largestPart p - tDiag p ∉ p.parts.erase (largestPart p) :=
    fun h => hlo_not (Multiset.mem_of_mem_erase h)
  have ht_not : tDiag p ∉ p.parts := by
    intro h; have := sPart_le hnz h; omega
  have ht_erase : tDiag p ∉ p.parts.erase (largestPart p) :=
    fun h => ht_not (Multiset.mem_of_mem_erase h)
  have ht_ne_lo : tDiag p ≠ largestPart p - tDiag p := by omega
  refine Multiset.nodup_cons.mpr ⟨?_, Multiset.nodup_cons.mpr ⟨hlo_ne, h1⟩⟩
  intro hmem
  rcases Multiset.mem_cons.mp hmem with he | he
  · exact ht_ne_lo he
  · exact ht_erase he

/-! ### The two moves as honest partitions -/

/-- The DOWN move as an honest `Nat.Partition m` (positivity and sum discharged, the sum via
`franklin_sum_invariant_down`). Requires the non-fixed hypothesis `2s ≠ L+1`. -/
noncomputable def downPart (p : m.Partition) (hnz : p.parts ≠ 0)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) : m.Partition where
  parts := downMs p
  parts_pos := by
    intro x hx
    rw [downMs, Multiset.mem_cons] at hx
    rcases hx with h | h
    · omega
    · exact p.parts_pos (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase h))
  parts_sum := by
    have hs_mem : sPart p ∈ p.parts := sPart_mem hnz
    have hd_mem : largestPart p - sPart p + 1 ∈ p.parts := d_mem hnz hst
    have hsp : 0 < sPart p := sPart_pos hnz
    have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
    have hdne : largestPart p - sPart p + 1 ≠ sPart p := by omega
    have hd_in : largestPart p - sPart p + 1 ∈ p.parts.erase (sPart p) :=
      (Multiset.mem_erase_of_ne hdne).mpr hd_mem
    have hsum := franklin_sum_invariant_down p.parts hs_mem hd_in rfl
    rw [Multiset.sum_add, Multiset.sum_singleton, p.parts_sum] at hsum
    rw [downMs, Multiset.sum_cons]
    omega

/-- The UP move as an honest `Nat.Partition m` (positivity and sum discharged, the sum via
`franklin_sum_invariant_up`). Only needs the case hypothesis `t < s`. -/
noncomputable def upPart (p : m.Partition) (hnz : p.parts ≠ 0)
    (hst : tDiag p < sPart p) : m.Partition where
  parts := upMs p
  parts_pos := by
    intro x hx
    rw [upMs, Multiset.mem_cons, Multiset.mem_cons] at hx
    have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
    have htL : tDiag p < largestPart p := by omega
    rcases hx with h | h | h
    · rw [h]; have := one_le_tDiag hnz; omega
    · rw [h]; omega
    · exact p.parts_pos (Multiset.mem_of_mem_erase h)
  parts_sum := by
    have hL_mem : largestPart p ∈ p.parts := largestPart_mem hnz
    have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
    have htL : tDiag p < largestPart p := by omega
    have habc : tDiag p + (largestPart p - tDiag p) = largestPart p := by omega
    have hsum := franklin_sum_invariant_up p.parts hL_mem habc
    rw [Multiset.sum_add, Multiset.sum_cons, Multiset.sum_singleton, p.parts_sum] at hsum
    rw [upMs, Multiset.sum_cons, Multiset.sum_cons]
    omega

/-! ### The part count changes by one -/

/-- The down move drops the part count by one: `#parts p = #(downMs p) + 1`. -/
theorem downMs_card {p : m.Partition} (hnz : p.parts ≠ 0)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    Multiset.card p.parts = Multiset.card (downMs p) + 1 := by
  have hs_mem : sPart p ∈ p.parts := sPart_mem hnz
  have hd_mem : largestPart p - sPart p + 1 ∈ p.parts := d_mem hnz hst
  have hsp : 0 < sPart p := sPart_pos hnz
  have hsL : sPart p ≤ largestPart p := sPart_le_largest hnz
  have hdne : largestPart p - sPart p + 1 ≠ sPart p := by omega
  have hd_in : largestPart p - sPart p + 1 ∈ p.parts.erase (sPart p) :=
    (Multiset.mem_erase_of_ne hdne).mpr hd_mem
  have e2 := Multiset.card_erase_add_one hd_in
  have e1 := Multiset.card_erase_add_one hs_mem
  rw [downMs, Multiset.card_cons]
  omega

/-- The up move raises the part count by one: `#(upMs p) = #parts p + 1`. -/
theorem upMs_card {p : m.Partition} (hnz : p.parts ≠ 0) :
    Multiset.card (upMs p) = Multiset.card p.parts + 1 := by
  have hL_mem : largestPart p ∈ p.parts := largestPart_mem hnz
  have e1 := Multiset.card_erase_add_one hL_mem
  rw [upMs, Multiset.card_cons, Multiset.card_cons]
  omega

/-! ### The sign reverses -/

/-- The down move reverses the sign: `signOf (downPart p …) = − signOf p`. -/
theorem downPart_sign {p : m.Partition} (hnz : p.parts ≠ 0)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    signOf (downPart p hnz hst hov) = - signOf p := by
  have hc : Multiset.card p.parts = Multiset.card (downMs p) + 1 := downMs_card hnz hst hov
  show (-1 : ℤ) ^ (Multiset.card (downMs p)) = -(-1 : ℤ) ^ (Multiset.card p.parts)
  rw [hc, pow_succ]
  ring

/-- The up move reverses the sign: `signOf (upPart p …) = − signOf p`. -/
theorem upPart_sign {p : m.Partition} (hnz : p.parts ≠ 0) (hst : tDiag p < sPart p) :
    signOf (upPart p hnz hst) = - signOf p := by
  have hc : Multiset.card (upMs p) = Multiset.card p.parts + 1 := upMs_card hnz
  show (-1 : ℤ) ^ (Multiset.card (upMs p)) = -(-1 : ℤ) ^ (Multiset.card p.parts)
  rw [hc, pow_succ]
  ring

/-! ### The moves have no fixed point -/

/-- The down move is not the identity: it changes the part count. -/
theorem downPart_ne {p : m.Partition} (hnz : p.parts ≠ 0)
    (hst : sPart p ≤ tDiag p) (hov : 2 * sPart p ≠ largestPart p + 1) :
    downPart p hnz hst hov ≠ p := by
  intro h
  have hc : Multiset.card p.parts = Multiset.card (downMs p) + 1 := downMs_card hnz hst hov
  have hcard : Multiset.card (downMs p) = Multiset.card p.parts :=
    congrArg Multiset.card (congrArg Nat.Partition.parts h)
  omega

/-- The up move is not the identity: it changes the part count. -/
theorem upPart_ne {p : m.Partition} (hnz : p.parts ≠ 0) (hst : tDiag p < sPart p) :
    upPart p hnz hst ≠ p := by
  intro h
  have hc : Multiset.card (upMs p) = Multiset.card p.parts + 1 := upMs_card hnz
  have hcard : Multiset.card (upMs p) = Multiset.card p.parts :=
    congrArg Multiset.card (congrArg Nat.Partition.parts h)
  omega

/-! ### Franklin's involution as one concrete map -/

/-- Franklin's involution `φ` as a single concrete map, by the classical case split
`sPart p ≤ tDiag p` (down move) versus `sPart p > tDiag p` (up move). The non-overlap
data is threaded as case-guarded implications. -/
noncomputable def phi (p : m.Partition) (hnz : p.parts ≠ 0)
    (hd : sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : tDiag p < sPart p → largestPart p ≠ 2 * tDiag p) : m.Partition :=
  if h : sPart p ≤ tDiag p then downPart p hnz h (hd h)
  else upPart p hnz (not_le.mp h)

/-- **Field `map_sign`.** Franklin's map reverses the sign. -/
theorem phi_sign (p : m.Partition) (hnz : p.parts ≠ 0)
    (hd : sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : tDiag p < sPart p → largestPart p ≠ 2 * tDiag p) :
    signOf (phi p hnz hd hu) = - signOf p := by
  unfold phi
  split_ifs with h
  · exact downPart_sign hnz h (hd h)
  · exact upPart_sign hnz (not_le.mp h)

/-- **`Nodup` half of field `map_mem`.** Franklin's map lands on a distinct partition. -/
theorem phi_parts_nodup (p : m.Partition) (hnz : p.parts ≠ 0) (hnd : p.parts.Nodup)
    (hd : sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : tDiag p < sPart p → largestPart p ≠ 2 * tDiag p) :
    (phi p hnz hd hu).parts.Nodup := by
  unfold phi
  split_ifs with h
  · exact downMs_nodup hnz hnd
  · exact upMs_nodup hnz hnd (not_le.mp h) (hu (not_le.mp h))

/-- **Field `map_ne`.** Franklin's map has no fixed point (the part count changes). -/
theorem phi_ne (p : m.Partition) (hnz : p.parts ≠ 0)
    (hd : sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : tDiag p < sPart p → largestPart p ≠ 2 * tDiag p) :
    phi p hnz hd hu ≠ p := by
  unfold phi
  split_ifs with h
  · exact downPart_ne hnz h (hd h)
  · exact upPart_ne hnz (not_le.mp h)

/-! ### Assembling `map_mem`, and the reduction -/

/-- A partition in `distincts m \ fixedPart m` has distinct parts. -/
theorem nodup_of_sdiff {p : m.Partition} (hp : p ∈ distincts m \ fixedPart m) : p.parts.Nodup := by
  have h1 := (Finset.mem_sdiff.mp hp).1
  simp only [distincts, Finset.mem_filter, Finset.mem_univ, true_and] at h1
  exact h1

/-- **Field `map_mem`, assembled.** Given fixed-set stability (`hnotfixed`), Franklin's image
lands back in `distincts m \ fixedPart m`; the `Nodup` half is proved (`phi_parts_nodup`). -/
theorem phiMem
    (hnz : ∀ p, p ∈ distincts m \ fixedPart m → p.parts ≠ 0)
    (hd : ∀ p, p ∈ distincts m \ fixedPart m →
      sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : ∀ p, p ∈ distincts m \ fixedPart m →
      tDiag p < sPart p → largestPart p ≠ 2 * tDiag p)
    (hnotfixed : ∀ p (hp : p ∈ distincts m \ fixedPart m),
      phi p (hnz p hp) (hd p hp) (hu p hp) ∉ fixedPart m) :
    ∀ p (hp : p ∈ distincts m \ fixedPart m),
      phi p (hnz p hp) (hd p hp) (hu p hp) ∈ distincts m \ fixedPart m := by
  intro p hp
  rw [Finset.mem_sdiff]
  refine ⟨?_, hnotfixed p hp⟩
  simp only [distincts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact phi_parts_nodup p (hnz p hp) (nodup_of_sdiff hp) (hd p hp) (hu p hp)

/-- **The reduction to the residual glue.** Given the fixed-point classification
(`hd`, `hu`), fixed-set stability (`hnotfixed`), and global involutivity (`hinv`),
Franklin's involution `FranklinMap m` is assembled. The fields `map_sign`, `map_ne`,
and the `Nodup` half of `map_mem` are discharged here from the concrete `phi`. -/
noncomputable def franklinMap_of (m : ℕ)
    (hnz : ∀ p, p ∈ distincts m \ fixedPart m → p.parts ≠ 0)
    (hd : ∀ p, p ∈ distincts m \ fixedPart m →
      sPart p ≤ tDiag p → 2 * sPart p ≠ largestPart p + 1)
    (hu : ∀ p, p ∈ distincts m \ fixedPart m →
      tDiag p < sPart p → largestPart p ≠ 2 * tDiag p)
    (hnotfixed : ∀ p (hp : p ∈ distincts m \ fixedPart m),
      phi p (hnz p hp) (hd p hp) (hu p hp) ∉ fixedPart m)
    (hinv : ∀ p (hp : p ∈ distincts m \ fixedPart m),
      phi (phi p (hnz p hp) (hd p hp) (hu p hp))
        (hnz _ (phiMem hnz hd hu hnotfixed p hp))
        (hd _ (phiMem hnz hd hu hnotfixed p hp))
        (hu _ (phiMem hnz hd hu hnotfixed p hp)) = p) :
    FranklinMap m where
  map := fun p hp => phi p (hnz p hp) (hd p hp) (hu p hp)
  map_mem := fun p hp => phiMem hnz hd hu hnotfixed p hp
  map_sign := fun p hp => phi_sign p (hnz p hp) (hd p hp) (hu p hp)
  map_ne := fun p hp => phi_ne p (hnz p hp) (hd p hp) (hu p hp)
  map_involutive := hinv

end Brockian.FranklinMapConstruction
