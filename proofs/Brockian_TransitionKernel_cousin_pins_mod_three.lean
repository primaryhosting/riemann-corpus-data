/-
  Brockian/TransitionKernel.lean — the gap-g transition kernel and the
  constellation transition tables.

  The finite-state substrate behind the q−ν admissibility law: over the
  wheel `ZMod q` a gap `g` induces a transition kernel `K i j` that fires
  exactly on admissible steps `i → i+g` with both endpoints nonzero. The
  double sum of the kernel counts the admissible start residues
  (`totalSum_eq`), which is `q − 2` whenever `g ≠ 0` (`totalSum_count`).
  Specialising the kernel to the small wheel primes recovers the
  constellation classification (twin / cousin / sexy / quadruplet), and
  the twin case exhibits the single forbidden nonzero transition
  (`forbidden_transition`, `twin_admissible_singleton`).

  Provenance: transition/admissible-start double-count from
  ConfigurationCount.lean (GeometricArithmetic, fully proven); the
  constellation classification mirrors ConstellationAlphabet.lean targets
  CA-1/CA-2/CA-3/CA-4/CA-5 — re-proved here by kernel `decide`, never
  shipped as `sorry`.

  Verification:
    - `#print axioms`  : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.TransitionKernel

open Finset

/-! ## 1. The abstract finite-state transition kernel -/

/-- The gap-`g` transition kernel on the wheel `ZMod q`. `kernel q g i j = 1`
exactly when the step `i → j` is an admissible transition: `j = i + g` and
both endpoints are nonzero (i.e. avoid the struck ray `0`). Otherwise `0`. -/
def kernel (q : ℕ) [NeZero q] (g : ZMod q) (i j : ZMod q) : ℕ :=
  if i ≠ 0 ∧ j ≠ 0 ∧ j = i + g then 1 else 0

/-- The admissible start residues for gap `g`: those `i` with `i ≠ 0` and
`i + g ≠ 0`. This is the support of the kernel (the transition table). -/
def admissibleStarts (q : ℕ) [NeZero q] (g : ZMod q) : Finset (ZMod q) :=
  univ.filter (fun i => i ≠ 0 ∧ i + g ≠ 0)

/-! ## 2. Complete transition support -/

/-- Membership in the transition table is exactly the two nonzero-endpoint
conditions. -/
@[simp] theorem mem_admissibleStarts (q : ℕ) [NeZero q] (g i : ZMod q) :
    i ∈ admissibleStarts q g ↔ i ≠ 0 ∧ i + g ≠ 0 := by
  simp [admissibleStarts]

/-- **Complete transition support.** For each fixed source `i`, the kernel row
sums to `1` when `i` is an admissible start and to `0` otherwise: every
admissible residue has exactly one outgoing transition (to `i + g`), and every
inadmissible residue has none. -/
theorem kernel_row_sum (q : ℕ) [NeZero q] (g i : ZMod q) :
    ∑ j, kernel q g i j = if i ≠ 0 ∧ i + g ≠ 0 then 1 else 0 := by
  have hpt : ∀ j : ZMod q, kernel q g i j
      = if j = i + g then (if i ≠ 0 ∧ i + g ≠ 0 then 1 else 0) else 0 := by
    intro j
    unfold kernel
    by_cases hj : j = i + g
    · subst hj
      by_cases hi : i = 0
      · simp [hi]
      · simp [hi]
    · simp [hj]
  simp only [hpt]
  rw [Finset.sum_ite_eq' univ (i + g) (fun _ => if i ≠ 0 ∧ i + g ≠ 0 then 1 else 0)]
  simp

/-! ## 3. The transition-kernel double count -/

/-- **totalSum_eq.** The double sum of the gap-`g` transition kernel over the
wheel equals the number of admissible start residues: the kernel is the
indicator of the admissible transition table, so summing it counts that table. -/
theorem totalSum_eq (q : ℕ) [NeZero q] (g : ZMod q) :
    ∑ i, ∑ j, kernel q g i j = (admissibleStarts q g).card := by
  simp only [kernel_row_sum]
  rw [admissibleStarts, Finset.card_filter]

/-- **totalSum_count.** For any nonzero gap the transition kernel double sum is
exactly `q − 2` — the universal `q − ν` law realised as a kernel trace. -/
theorem totalSum_count (q : ℕ) [NeZero q] (g : ZMod q) (hg : g ≠ 0) :
    ∑ i, ∑ j, kernel q g i j = q - 2 := by
  rw [totalSum_eq]
  have hset : admissibleStarts q g = (univ : Finset (ZMod q)) \ {0, -g} := by
    ext i
    simp only [mem_admissibleStarts, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · rintro ⟨h0, hg0⟩
      exact ⟨h0, fun h => hg0 (add_eq_zero_iff_eq_neg.mpr h)⟩
    · rintro ⟨h0, hng⟩
      exact ⟨h0, fun h => hng (add_eq_zero_iff_eq_neg.mp h)⟩
  rw [hset]
  have hpair : ({0, -g} : Finset (ZMod q)).card = 2 :=
    Finset.card_pair (by
      intro h
      exact hg (neg_eq_zero.mp h.symm))
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by
    rw [Finset.card_univ, ZMod.card]
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.univ_inter, hcard, hpair]

/-! ## 4. The constellation transition tables

The small-wheel specialisations. Each classification is a decidable fact over a
finite `ZMod p`, proved by kernel evaluation (never `native_decide`). These
mirror the ConstellationAlphabet targets CA-1..CA-5. -/

/-- **Twin pinning (gap 2 mod 3).** A twin start above the wheel is forced to
the single residue `2`: `i` admits a twin transition iff `i = 2`. -/
theorem twin_pins_mod_three (a : ZMod 3) :
    (a ≠ 0 ∧ a + 2 ≠ 0) ↔ a = 2 := by decide +revert

/-- **Cousin pinning (gap 4 mod 3, CA-1).** A cousin start is pinned to `1`. -/
theorem cousin_pins_mod_three (a : ZMod 3) :
    (a ≠ 0 ∧ a + 4 ≠ 0) ↔ a = 1 := by decide +revert

/-- **Sexy freedom (gap 6 mod 3, CA-2).** A sexy start is free at the wheel
prime `3`: both nonzero classes survive. -/
theorem sexy_free_mod_three (a : ZMod 3) :
    (a ≠ 0 ∧ a + 6 ≠ 0) ↔ (a = 1 ∨ a = 2) := by decide +revert

/-- **Quadruplet pinning (pattern {0,2,6,8} mod 5).** A prime-quadruplet start
is pinned to the single residue `1` mod `5`. -/
theorem quadruplet_pins_mod_five (a : ZMod 5) :
    (a ≠ 0 ∧ a + 2 ≠ 0 ∧ a + 6 ≠ 0 ∧ a + 8 ≠ 0) ↔ a = 1 := by decide +revert

/-- **Cousin run cap (CA-3).** No `+3`-run of length 3 fits the admissible
cousin classes `{2,3,4}` mod 5: the cousin cap is 2. -/
theorem cousin_run_cap :
    ¬ ∃ a : ZMod 5, ({a, a + 3, a + 6} : Finset (ZMod 5)) ⊆
      ({2, 3, 4} : Finset (ZMod 5)) := by decide

/-- **Sexy run cap (CA-4).** Three consecutive integers cannot all avoid `0`
mod 3: the sexy cap is 2. -/
theorem sexy_run_cap :
    ¬ ∃ a : ZMod 3, ({a, a + 1, a + 2} : Finset (ZMod 3)) ⊆
      ({1, 2} : Finset (ZMod 3)) := by decide

/-- **Gap-10 opens the fourth door (CA-5).** When `5 ∣ g` a `+3`-run of length 4
exists mod 5 (all four nonzero classes admissible), but length 5 does not. -/
theorem gap10_run_cap :
    (∃ a : ZMod 5, ({a, a + 3, a + 6, a + 9} : Finset (ZMod 5)) ⊆
      ({1, 2, 3, 4} : Finset (ZMod 5))) ∧
    ¬ ∃ a : ZMod 5, ({a, a + 3, a + 6, a + 9, a + 12} : Finset (ZMod 5)) ⊆
      ({1, 2, 3, 4} : Finset (ZMod 5)) := by decide

/-! ## 5. Twin exclusion — the single forbidden transition -/

/-- **forbidden_transition.** In the twin kernel (gap 2 mod 3) the nonzero
residue `1` has *no* admissible outgoing transition: the step `1 → 1 + 2 = 0`
is forbidden. This is the one exclusion that pins the twin comb to `3ℤ`. -/
theorem forbidden_transition : ∀ j : ZMod 3, kernel 3 2 1 j = 0 := by decide

/-- **twin_admissible_singleton.** The twin transition table mod 3 is exactly the
singleton `{2}`: only residue `2` starts an admissible twin step. -/
theorem twin_admissible_singleton : admissibleStarts 3 2 = {2} := by decide

/-- **twin_table_card.** The twin transition table mod 3 has exactly one entry —
the `q − 2 = 1` law at the wheel prime `3`. -/
theorem twin_table_card : (admissibleStarts 3 2).card = 1 := by decide

/-- **brockian_table_card.** The Brockian case: mod 5 the twin transition table
has exactly three entries (`q − 2 = 3`). -/
theorem brockian_table_card : (admissibleStarts 5 2).card = 3 := by decide

end Brockian.TransitionKernel
