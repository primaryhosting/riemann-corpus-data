import Mathlib

/-!
# Brockian Figurate Numbers — the full polygonal family (division-free)

This module extends the Brockian "pentagonal law" strand to the full family of
polygonal (figurate) numbers.  Following the existing `Brockian.Pentagonal`
module — where `pent2 k = k(3k-1) = 2 · pent k` gives a division-free "doubled"
form so that `ring` can discharge identities over `ℤ` for ALL `k` — we work
throughout with the doubled figurate numbers:

* `tri2  k = k(k+1)       = 2 · T(k)`  (triangular)
* `pent2 k = k(3k-1)      = 2 · P(k)`  (pentagonal)
* `hex2  k = k(4k-2)      = 2 · H(k)`  (hexagonal, `= 2k(2k-1)`)
* `sq    k = k·k          = k²`         (square, already integral)

Every general theorem below is fully universally quantified over `k : ℤ` and is
proved by `unfold …; ring` — no `decide`, no integer division, no `sorry`,
axiom-clean.
-/

namespace Brockian.Figurate

/-- Doubled triangular number: `tri2 k = k(k+1) = 2 · T(k)`. -/
def tri2  (k : ℤ) : ℤ := k * (k + 1)

/-- Doubled pentagonal number: `pent2 k = k(3k-1) = 2 · P(k)`. -/
def pent2 (k : ℤ) : ℤ := k * (3 * k - 1)

/-- Doubled hexagonal number: `hex2 k = k(4k-2) = 2k(2k-1) = 2 · H(k)`. -/
def hex2  (k : ℤ) : ℤ := k * (4 * k - 2)

/-- Square number: `sq k = k² = k·k` (already integral, no doubling needed). -/
def sq    (k : ℤ) : ℤ := k * k

/-! ### Concrete tabulated values (grounding, proved by `decide`). -/

theorem tri2_3  : tri2  3 = 12 := by decide
theorem tri2_2  : tri2  2 = 6  := by decide
theorem pent2_3 : pent2 3 = 24 := by decide
theorem pent2_2 : pent2 2 = 10 := by decide
theorem hex2_3  : hex2  3 = 30 := by decide
theorem sq_3    : sq    3 = 9  := by decide

/-- A small grounding table: `T(3)=6, P(3)=12, H(3)=15, 3²=9` in doubled form. -/
theorem figurate_values :
    tri2 3 = 12 ∧ pent2 3 = 24 ∧ hex2 3 = 30 ∧ sq 3 = 9 :=
  ⟨tri2_3, pent2_3, hex2_3, sq_3⟩

/-! ### The general `∀k ∈ ℤ` structural identities (the centerpiece).

Each is division-free in doubled form, so `ring` proves it for ALL `k : ℤ`. -/

/-- **Anchor.** Every hexagonal number is triangular: `H(k) = T(2k-1)`.
    In doubled form `hex2 k = k(4k-2) = (2k-1)(2k) = tri2 (2k-1)`. -/
theorem hex2_eq_tri2_odd (k : ℤ) : hex2 k = tri2 (2 * k - 1) := by
  unfold hex2 tri2; ring

/-- Pentagonal decomposition: `pent2 k = tri2 (k-1) + 2 · sq k`.
    (Doubled form of the classic `P(k) = T(k-1) + k²`; the square term keeps
    its factor `2` because `sq` is not doubled.) -/
theorem pent2_decomp (k : ℤ) : pent2 k = tri2 (k - 1) + 2 * sq k := by
  unfold pent2 tri2 sq; ring

/-- Triangular recurrence: `tri2 (k+1) − tri2 k = 2(k+1)`
    (i.e. `T(k+1) − T(k) = k+1`). -/
theorem tri2_succ (k : ℤ) : tri2 (k + 1) - tri2 k = 2 * (k + 1) := by
  unfold tri2; ring

/-- Hexagonal recurrence: `hex2 (k+1) − hex2 k = 8k + 2`
    (i.e. `H(k+1) − H(k) = 4k+1`). -/
theorem hex2_succ (k : ℤ) : hex2 (k + 1) - hex2 k = 8 * k + 2 := by
  unfold hex2; ring

/-- Pentagonal recurrence: `pent2 (k+1) − pent2 k = 6k + 2`
    (i.e. `P(k+1) − P(k) = 3k+1`). -/
theorem pent2_succ (k : ℤ) : pent2 (k + 1) - pent2 k = 6 * k + 2 := by
  unfold pent2; ring

/-- Two squares as a triangular pair: `2 · sq k = tri2 k + tri2 (k-1)`
    (i.e. `2k² = k(k+1) + (k-1)k` — a division-free "sum of consecutive
    triangulars" identity). -/
theorem two_sq_eq_tri2_pair (k : ℤ) : 2 * sq k = tri2 k + tri2 (k - 1) := by
  unfold sq tri2; ring

/-- Hexagonal–pentagonal link: `hex2 k = pent2 k + tri2 (k-1)`
    (the hexagonal number exceeds the pentagonal one by exactly `T(k-1)`). -/
theorem hex2_eq_pent2_add (k : ℤ) : hex2 k = pent2 k + tri2 (k - 1) := by
  unfold hex2 pent2 tri2; ring

end Brockian.Figurate
