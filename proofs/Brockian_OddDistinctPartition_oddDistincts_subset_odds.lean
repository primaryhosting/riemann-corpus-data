/-
  Brockian/OddDistinctPartition.lean — EULER'S ODD = DISTINCT PARTITIONS
  identity, wired from Mathlib (Glaisher / Freek's 100 Theorems #45).

  Euler's classical partition theorem asserts that for every natural number `n`,

        #{ partitions of n into odd parts }
          = #{ partitions of n into distinct parts }.

  Mathlib 4.32 already contains a complete proof as
  `Nat.Partition.card_odds_eq_card_distincts`, obtained as the `m = 2` special
  case of Glaisher's theorem
  `Nat.Partition.card_restricted_eq_card_countRestricted`
  (parts not divisible by `m` ↔ no part repeated `m` or more times), via equal
  generating functions in `ℤ⟦X⟧`.

  This module is the Brockian ROADMAP WIRE for that fact, together with a solid
  finite/combinatorial packaging layer that does not re-prove Glaisher from
  scratch but makes the identity usable downstream (membership laws, base cases,
  subset bounds, power-series equality of counting series).

  ## What is proved  (axioms ⊆ {propext, Classical.choice, Quot.sound})
  * `euler_odd_eq_distinct`     — Euler: `#(odds n) = #(distincts n)` (Mathlib wire).
  * `glaisher`                  — Glaisher: restricted vs countRestricted (Mathlib wire).
  * `countRestricted_two_eq_distincts` — `countRestricted n 2 = distincts n`.
  * `mem_odds_iff`              — membership: odds ↔ every part is odd.
  * `mem_distincts_iff`         — membership: distincts ↔ parts are Nodup.
  * `parts_odd_of_mem_odds`     — every part of an odds-partition is odd.
  * `parts_nodup_of_mem_distincts` — parts of a distincts-partition are Nodup.
  * `odds_zero_card` / `distincts_zero_card` — both sides equal 1 at `n = 0`.
  * `odds_one_card` / `distincts_one_card`   — both sides equal 1 at `n = 1`.
  * `oddDistincts_subset_odds` / `oddDistincts_subset_distincts` — intersection ⊆.
  * `card_oddDistincts_le_odds` / `card_oddDistincts_le_distincts` — card bounds.
  * `card_odds_le_partition` / `card_distincts_le_partition` — ≤ total `p(n)`.
  * `card_distincts_le_powerset` — distincts inject into subsets of `{1,…,n}`.
  * `powerSeries_odds_eq_distincts` — counting series equality in `ℤ⟦X⟧`.

  ## What is NOT proved / claimed
  * A new combinatorial bijection (Glaisher/Euler bijection is generating-function
    based in Mathlib; we do not construct Glaisher's map here).
  * Franklin's involution / the pentagonal number theorem (see
    `PentagonalTheoremFranklin`).
  * Closed forms for `p_odd(n)` or `p_distinct(n)` as named sequences beyond
    the identity and base cases.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.OddDistinctPartition

open Nat.Partition Finset PowerSeries

/-! ## Mathlib wires: Euler and Glaisher -/

/-- **Euler's odd = distinct partitions theorem** (Freek's 100 Theorems #45).

The number of partitions of `n` into odd parts equals the number of partitions
of `n` into distinct parts. Wired from Mathlib's
`Nat.Partition.card_odds_eq_card_distincts` (Glaisher at `m = 2`). -/
theorem euler_odd_eq_distinct (n : ℕ) : #(odds n) = #(distincts n) :=
  card_odds_eq_card_distincts n

/-- **Glaisher's theorem.** For `0 < m`, the number of partitions of `n` into
parts not divisible by `m` equals the number of partitions in which no part is
repeated `m` or more times. Wired from
`Nat.Partition.card_restricted_eq_card_countRestricted`. -/
theorem glaisher (n : ℕ) {m : ℕ} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) :=
  card_restricted_eq_card_countRestricted n hm

/-- Mathlib identification: distinct parts ⇔ no part used 2 or more times. -/
theorem countRestricted_two_eq_distincts (n : ℕ) :
    countRestricted n 2 = distincts n :=
  countRestricted_two n

/-- Euler as the explicit `m = 2` instance of Glaisher, rewritten without the
`odds`/`distincts` abbreviations (parts not divisible by 2 = odd parts;
count-restricted by 2 = distinct parts). -/
theorem euler_via_glaisher (n : ℕ) :
    #(restricted n (¬ 2 ∣ ·)) = #(countRestricted n 2) :=
  glaisher n (by decide)

/-! ## Membership characterizations -/

/-- A partition lies in `odds n` iff every part is odd. -/
theorem mem_odds_iff {n : ℕ} (p : n.Partition) :
    p ∈ odds n ↔ ∀ i ∈ p.parts, Odd i := by
  simp [odds, restricted, Nat.not_even_iff_odd]

/-- A partition lies in `distincts n` iff its parts multiset is nodup. -/
theorem mem_distincts_iff {n : ℕ} (p : n.Partition) :
    p ∈ distincts n ↔ p.parts.Nodup := by
  simp [distincts]

/-- Every part of an odds-partition is odd. -/
theorem parts_odd_of_mem_odds {n : ℕ} {p : n.Partition} (hp : p ∈ odds n)
    {i : ℕ} (hi : i ∈ p.parts) : Odd i :=
  (mem_odds_iff p).1 hp i hi

/-- Parts of a distincts-partition form a nodup multiset. -/
theorem parts_nodup_of_mem_distincts {n : ℕ} {p : n.Partition}
    (hp : p ∈ distincts n) : p.parts.Nodup :=
  (mem_distincts_iff p).1 hp

/-! ## Base cases `n = 0` and `n = 1` -/

/-- At `n = 0` the unique (empty) partition has all-odd parts vacuously, so
`#(odds 0) = 1`. -/
theorem odds_zero_card : #(odds 0) = 1 := by
  have hmem : ∀ p : Nat.Partition 0, p ∈ odds 0 := by
    intro p
    simp [mem_odds_iff, Nat.Partition.partition_zero_parts]
  have h : odds 0 = univ := eq_univ_iff_forall.mpr hmem
  rw [h, card_univ, Fintype.card_unique]

/-- At `n = 0` the unique (empty) partition has nodup parts, so
`#(distincts 0) = 1`. -/
theorem distincts_zero_card : #(distincts 0) = 1 := by
  have hmem : ∀ p : Nat.Partition 0, p ∈ distincts 0 := by
    intro p
    simp [mem_distincts_iff, Nat.Partition.partition_zero_parts]
  have h : distincts 0 = univ := eq_univ_iff_forall.mpr hmem
  rw [h, card_univ, Fintype.card_unique]

/-- At `n = 1` the unique partition is `{1}`, which is odd, so `#(odds 1) = 1`. -/
theorem odds_one_card : #(odds 1) = 1 := by
  have hmem : ∀ p : Nat.Partition 1, p ∈ odds 1 := fun p => by
    rw [mem_odds_iff, Nat.Partition.partition_one_parts]
    intro i hi
    have hi' : i = 1 := by simpa using hi
    rw [hi']
    decide
  have h : odds 1 = univ := eq_univ_iff_forall.mpr hmem
  rw [h, card_univ, Fintype.card_unique]

/-- At `n = 1` the unique partition is `{1}`, which is nodup, so
`#(distincts 1) = 1`. -/
theorem distincts_one_card : #(distincts 1) = 1 := by
  have hmem : ∀ p : Nat.Partition 1, p ∈ distincts 1 := by
    intro p
    simp [mem_distincts_iff, Nat.Partition.partition_one_parts]
  have h : distincts 1 = univ := eq_univ_iff_forall.mpr hmem
  rw [h, card_univ, Fintype.card_unique]

/-- Consistency of Euler at the base: both sides equal `1` at `n = 0`. -/
theorem euler_zero : #(odds 0) = #(distincts 0) ∧ #(odds 0) = 1 :=
  ⟨euler_odd_eq_distinct 0, odds_zero_card⟩

/-- Consistency of Euler at the base: both sides equal `1` at `n = 1`. -/
theorem euler_one : #(odds 1) = #(distincts 1) ∧ #(odds 1) = 1 :=
  ⟨euler_odd_eq_distinct 1, odds_one_card⟩

/-! ## Odd-and-distinct intersection and crude bounds -/

/-- Odd-and-distinct partitions are a subset of odd partitions. -/
theorem oddDistincts_subset_odds (n : ℕ) : oddDistincts n ⊆ odds n :=
  inter_subset_left

/-- Odd-and-distinct partitions are a subset of distinct partitions. -/
theorem oddDistincts_subset_distincts (n : ℕ) : oddDistincts n ⊆ distincts n :=
  inter_subset_right

/-- `#(oddDistincts n) ≤ #(odds n)`. -/
theorem card_oddDistincts_le_odds (n : ℕ) : #(oddDistincts n) ≤ #(odds n) :=
  card_le_card (oddDistincts_subset_odds n)

/-- `#(oddDistincts n) ≤ #(distincts n)`. -/
theorem card_oddDistincts_le_distincts (n : ℕ) :
    #(oddDistincts n) ≤ #(distincts n) :=
  card_le_card (oddDistincts_subset_distincts n)

/-- Odd partitions are among all partitions: `#(odds n) ≤ p(n)`. -/
theorem card_odds_le_partition (n : ℕ) :
    #(odds n) ≤ Fintype.card (n.Partition) := by
  simpa [card_univ] using card_le_card (subset_univ (odds n))

/-- Distinct partitions are among all partitions: `#(distincts n) ≤ p(n)`. -/
theorem card_distincts_le_partition (n : ℕ) :
    #(distincts n) ≤ Fintype.card (n.Partition) := by
  simpa [card_univ] using card_le_card (subset_univ (distincts n))

/-- Every part of a partition of `n` lies in `{1, …, n}`. -/
theorem parts_subset_Icc {n : ℕ} (p : n.Partition) :
    p.parts.toFinset ⊆ Icc 1 n := by
  intro i hi
  rw [Multiset.mem_toFinset] at hi
  exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (p.parts_pos hi), le_of_mem_parts hi⟩

/-- On `distincts n`, the map `p ↦ p.parts.toFinset` is injective
(nodup + equal support ⇒ equal multisets). -/
theorem toFinset_inj_on_distincts {n : ℕ} {p q : n.Partition}
    (hp : p ∈ distincts n) (hq : q ∈ distincts n)
    (h : p.parts.toFinset = q.parts.toFinset) : p = q :=
  Nat.Partition.ext <|
    Multiset.Nodup.toFinset_inj (parts_nodup_of_mem_distincts hp)
      (parts_nodup_of_mem_distincts hq) h

/-- Distinct partitions inject into the powerset of `{1, …, n}` by forgetting
multiplicity (nodup ⇒ parts are a set). Hence
`#(distincts n) ≤ #(Icc 1 n).powerset`. -/
theorem card_distincts_le_powerset (n : ℕ) :
    #(distincts n) ≤ #((Icc 1 n).powerset) := by
  classical
  let f : n.Partition → Finset ℕ := fun p => p.parts.toFinset
  have hf : Set.MapsTo f ↑(distincts n) ↑((Icc 1 n).powerset) := by
    intro p _hp
    exact mem_powerset.mpr (parts_subset_Icc p)
  have hinj : Set.InjOn f ↑(distincts n) := by
    intro p hp q hq h
    exact toFinset_inj_on_distincts hp hq h
  exact card_le_card_of_injOn (s := distincts n) (t := (Icc 1 n).powerset) f hf hinj

/-! ## Counting generating functions agree -/

/-- The ordinary generating functions of the two counting sequences are equal
in `ℤ⟦X⟧`: coefficient-wise Euler supplies `#(odds n) = #(distincts n)`. -/
theorem powerSeries_odds_eq_distincts :
    (PowerSeries.mk fun n ↦ (#(odds n) : ℤ)) =
      PowerSeries.mk fun n ↦ (#(distincts n) : ℤ) := by
  ext n
  simp [euler_odd_eq_distinct n]

end Brockian.OddDistinctPartition
