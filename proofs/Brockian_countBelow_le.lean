/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *constellation* (or prime `k`-tuple pattern) is a tuple of integer shifts
`(h₁, …, h_k)`.  Its *local count* at a modulus `p` is the number of residues
`n` with `0 ≤ n < p` such that none of the shifted values `n + hᵢ` is divisible
by `p`.  This is the quantity `p - ν_p(H)` appearing in the singular series of
the Hardy–Littlewood prime `k`-tuple conjecture, where `ν_p(H)` is the number of
distinct residues occupied by the pattern mod `p`.

This file develops the local count from scratch and settles the case `k = 3`:
the local count of a triple equals `p` minus the number of *distinct* residues
among the three excluded classes `-hᵢ mod p`.  In particular a triple whose
shifts are pairwise incongruent mod `p` has local count exactly `p - 3`.

The development is self-contained (core Lean 4 only, no imports), so that the
required header comment can be the very first thing in the file.  (With Mathlib
available the same argument is the complement count
`Finset.card_univ_diff : (Finset.univ \ s).card = Fintype.card α - s.card`
together with `ZMod.card`, applied to the excluded set `{-h₁, -h₂, -h₃} ⊆ ZMod p`;
no single Mathlib lemma states the constellation local count itself.)
-/

namespace Brockian

/-! ## A counting operator -/

/-- `countBelow N f` is the number of naturals `n < N` with `f n = true`. -/
def countBelow (N : Nat) (f : Nat → Bool) : Nat :=
  match N with
  | 0 => 0
  | N + 1 => countBelow N f + (if f N then 1 else 0)

theorem countBelow_le (N : Nat) (f : Nat → Bool) : countBelow N f ≤ N := by
  induction N with
  | zero => simp [countBelow]
  | succ n ih => simp only [countBelow]; split <;> omega

/-- Counting is insensitive to the values of the predicate at or above `N`. -/
theorem countBelow_congr (N : Nat) (f g : Nat → Bool) (h : ∀ n, n < N → f n = g n) :
    countBelow N f = countBelow N g := by
  induction N with
  | zero => simp [countBelow]
  | succ n ih =>
    have hn : f n = g n := h n (by omega)
    simp only [countBelow, ih (fun m hm => h m (by omega)), hn]

/-- The complementary count. -/
theorem countBelow_not (N : Nat) (f : Nat → Bool) :
    countBelow N (fun n => !f n) = N - countBelow N f := by
  induction N with
  | zero => simp [countBelow]
  | succ n ih =>
    have hle := countBelow_le n f
    show (countBelow n fun n => !f n) + (if (!f n) = true then 1 else 0)
        = n + 1 - (countBelow n f + if f n = true then 1 else 0)
    rcases Bool.eq_false_or_eq_true (f n) with hf | hf <;> rw [hf] <;> simp [ih] <;> omega

theorem countBelow_singleton (N r : Nat) :
    countBelow N (fun n => n == r) = if r < N then 1 else 0 := by
  induction N with
  | zero => simp [countBelow]
  | succ n ih =>
    show countBelow n (fun n => n == r) + (if (n == r) = true then 1 else 0) = _
    rw [ih]
    by_cases h : n = r
    · subst h; simp
    · simp only [beq_iff_eq, h, if_false]
      have : ¬ (r = n) := fun hh => h hh.symm
      split <;> split <;> omega

/-- Counts add over disjoint predicates. -/
theorem countBelow_or_disjoint (N : Nat) (f g : Nat → Bool)
    (hd : ∀ n, f n = true → g n = false) :
    countBelow N (fun n => f n || g n) = countBelow N f + countBelow N g := by
  induction N with
  | zero => simp [countBelow]
  | succ n ih =>
    show (countBelow n fun n => f n || g n) + (if (f n || g n) = true then 1 else 0)
        = (countBelow n f + if f n = true then 1 else 0)
          + (countBelow n g + if g n = true then 1 else 0)
    rw [ih]
    rcases Bool.eq_false_or_eq_true (f n) with hf | hf <;>
      rcases Bool.eq_false_or_eq_true (g n) with hg | hg <;>
      rw [hf, hg] <;> simp <;> try omega
    · have := hd n hf; simp_all

/-! ## Counting two or three prescribed residues -/

/-- The number of distinct entries among `a, b, c`. -/
def distinctCount3 (a b c : Nat) : Nat :=
  if a = b then (if a = c then 1 else 2)
  else if a = c then 2
  else if b = c then 2 else 3

theorem countBelow_pair (p a b : Nat) (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    countBelow p (fun n => (n == a) || (n == b)) = 2 := by
  rw [countBelow_or_disjoint p _ _ (by intro n hn; simp_all),
    countBelow_singleton, countBelow_singleton, if_pos ha, if_pos hb]

/-- The number of `n < p` lying in the (multi)set `{r1, r2, r3}` is the number of
distinct entries of that triple. -/
theorem countBelow_three (p r1 r2 r3 : Nat) (h1 : r1 < p) (h2 : r2 < p) (h3 : r3 < p) :
    countBelow p (fun n => (n == r1) || (n == r2) || (n == r3)) = distinctCount3 r1 r2 r3 := by
  by_cases e12 : r1 = r2 <;> by_cases e13 : r1 = r3 <;> by_cases e23 : r2 = r3 <;>
    simp only [distinctCount3, e12, e13, e23]
  all_goals try omega
  · subst e12; subst e13
    simp only [Bool.or_self]
    rw [countBelow_singleton, if_pos h1]
    simp
  · subst e12
    have hfun : (fun n => (n == r1) || (n == r1) || (n == r3))
        = (fun n => (n == r1) || (n == r3)) := by
      funext n; simp
    rw [hfun, countBelow_pair p r1 r3 h1 h3 e13]
    simp
  · subst e13
    have hfun : (fun n => (n == r1) || (n == r2) || (n == r1))
        = (fun n => (n == r1) || (n == r2)) := by
      funext n; by_cases hn : n = r1 <;> by_cases hn2 : n = r2 <;> simp_all
    rw [hfun, countBelow_pair p r1 r2 h1 h2 e12, if_neg e12]
    simp
  · subst e23
    have hfun : (fun n => (n == r1) || (n == r2) || (n == r2))
        = (fun n => (n == r1) || (n == r2)) := by
      funext n; simp
    rw [hfun, countBelow_pair p r1 r2 h1 h2 e12]
    simp
  · rw [countBelow_or_disjoint p _ _
      (by intro n hn
          simp only [Bool.or_eq_true, beq_iff_eq] at hn ⊢
          rcases hn with rfl | rfl <;> simp_all),
      countBelow_singleton, if_pos h3, countBelow_pair p r1 r2 h1 h2 e12]
    simp

/-! ## Excluded residues of a shift -/

/-- The unique residue `n` mod `p` that the shift `h` kills, i.e. with `p ∣ n + h`. -/
def excludedResidue (p h : Nat) : Nat := (p - h % p) % p

theorem excludedResidue_lt (p h : Nat) (hp : 0 < p) : excludedResidue p h < p :=
  Nat.mod_lt _ hp

/-- De Morgan for a threefold conjunction of negations. -/
theorem bool_and_nots (x y z : Bool) : (!x && !y && !z) = !(x || y || z) := by
  cases x <;> cases y <;> cases z <;> rfl

/-- Characterisation of the excluded residue: for `n < p`, `p ∣ n + h` iff
`n = excludedResidue p h`. -/
theorem shifted_zero_iff (p h n : Nat) (hp : 0 < p) (hn : n < p) :
    ((n + h) % p = 0) ↔ n = excludedResidue p h := by
  have hr : h % p < p := Nat.mod_lt _ hp
  have hmod : (n + h) % p = (n + h % p) % p := by simp [Nat.add_mod]
  rw [hmod, excludedResidue]
  rcases Nat.eq_zero_or_pos (h % p) with h0 | h0
  · rw [h0]
    simp [Nat.mod_eq_of_lt hn, Nat.mod_self]
  · have hpr : p - h % p < p := by omega
    rw [Nat.mod_eq_of_lt hpr]
    rcases Nat.lt_or_ge (n + h % p) p with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hsub : (n + h % p) % p = n + h % p - p := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [hsub]
      omega

/-- Boolean form of `shifted_zero_iff`. -/
theorem shifted_beq (p h n : Nat) (hp : 0 < p) (hn : n < p) :
    ((n + h) % p == 0) = (n == excludedResidue p h) := by
  have hiff := shifted_zero_iff p h n hp hn
  cases hx : ((n + h) % p == 0) <;> cases hy : (n == excludedResidue p h) <;>
    simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at hx hy <;> first
      | rfl
      | (exact absurd (hiff.1 hx) hy)
      | (exact absurd (hiff.2 hy) hx)

/-- Shifts that are incongruent mod `p` have different excluded residues. -/
theorem excludedResidue_ne (p a b : Nat) (hp : 0 < p) (hab : a % p ≠ b % p) :
    excludedResidue p a ≠ excludedResidue p b := by
  have ha : a % p < p := Nat.mod_lt _ hp
  have hb : b % p < p := Nat.mod_lt _ hp
  unfold excludedResidue
  rcases Nat.eq_zero_or_pos (a % p) with h0 | h0 <;>
    rcases Nat.eq_zero_or_pos (b % p) with k0 | k0
  · omega
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [k0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : p - a % p < p),
      Nat.mod_eq_of_lt (by omega : p - b % p < p)]
    omega

/-! ## The local count of a `3`-tuple -/

/-- `n` survives the constellation `(h1, h2, h3)` at `p` when none of the shifted
values `n + hᵢ` is divisible by `p`. -/
def survivesK3 (p h1 h2 h3 n : Nat) : Bool :=
  !((n + h1) % p == 0) && !((n + h2) % p == 0) && !((n + h3) % p == 0)

/-- The local count at `p` of the constellation `(h1, h2, h3)`: the number of
residues `n < p` surviving all three shifts. -/
def localCountK3 (p h1 h2 h3 : Nat) : Nat := countBelow p (survivesK3 p h1 h2 h3)

/-- **Constellation local count, `k = 3`.**  For any modulus `p > 0` and any triple of
shifts `(h1, h2, h3)`, the number of residues `n < p` with `p ∤ n + hᵢ` for all `i`
equals `p` minus the number of *distinct* excluded residues `-hᵢ mod p`. -/
theorem ConstellationLocalCountK3 (p h1 h2 h3 : Nat) (hp : 0 < p) :
    localCountK3 p h1 h2 h3
      = p - distinctCount3 (excludedResidue p h1) (excludedResidue p h2)
          (excludedResidue p h3) := by
  have hkey : ∀ n, n < p →
      survivesK3 p h1 h2 h3 n
        = !((n == excludedResidue p h1) || (n == excludedResidue p h2)
            || (n == excludedResidue p h3)) := by
    intro n hn
    simp only [survivesK3, shifted_beq p h1 n hp hn, shifted_beq p h2 n hp hn,
      shifted_beq p h3 n hp hn]
    exact bool_and_nots _ _ _
  rw [localCountK3, countBelow_congr p _ _ hkey, countBelow_not,
    countBelow_three p _ _ _ (excludedResidue_lt p h1 hp) (excludedResidue_lt p h2 hp)
      (excludedResidue_lt p h3 hp)]

/-- **Generic case.**  If the three shifts are pairwise incongruent mod `p`, the local
count is exactly `p - 3`. -/
theorem ConstellationLocalCountK3_of_distinct (p h1 h2 h3 : Nat) (hp : 0 < p)
    (d12 : h1 % p ≠ h2 % p) (d13 : h1 % p ≠ h3 % p) (d23 : h2 % p ≠ h3 % p) :
    localCountK3 p h1 h2 h3 = p - 3 := by
  rw [ConstellationLocalCountK3 p h1 h2 h3 hp]
  have n12 := excludedResidue_ne p h1 h2 hp d12
  have n13 := excludedResidue_ne p h1 h3 hp d13
  have n23 := excludedResidue_ne p h2 h3 hp d23
  simp only [distinctCount3, if_neg n12, if_neg n13, if_neg n23]

/-- Sanity check: the admissible triple `(0, 2, 6)` occupies three distinct residues
mod `5`, leaving `5 - 3 = 2` surviving classes. -/
example : localCountK3 5 0 2 6 = 2 := by decide

/-- Sanity check: mod `2` the triple `(0, 2, 6)` occupies a single residue, so the
local count is `2 - 1 = 1`. -/
example : localCountK3 2 0 2 6 = 1 := by decide

end Brockian

