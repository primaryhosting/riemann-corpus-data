import Mathlib
namespace C3.BCon

def twinAdm {n : ℕ} (a : ZMod n) : Prop := IsUnit a ∧ IsUnit (a + 2)

open scoped Classical in
/-- The number of residues `a` mod `n` with both `a` and `a + 2` units is at most `n`.

Type-level fix: the statement needs `Fintype (ZMod n)`, which is only available for `n ≠ 0`,
so the instance `[NeZero n]` was added (equivalent to the given hypothesis `hn : 0 < n`,
which is therefore not used in the proof but kept as requested). Decidability of the
predicate is supplied classically. -/
theorem twin_adm_count_bound (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card ≤ n := by
  calc (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n := by simp [ZMod.card]

/-- Translation by `3` has no fixed point in `ZMod n` when `n > 3`. -/
theorem plus3_no_fixed (n : ℕ) (hn : 3 < n) (a : ZMod n) : a + 3 ≠ a := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  have h3 : (3 : ZMod n) = 0 := by
    have h' : a + 3 = a + 0 := by simpa using h
    exact add_left_cancel h'
  rw [show (3 : ZMod n) = ((3 : ℕ) : ZMod n) by push_cast; ring,
    ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

/-- There are exactly `4` nonzero residues modulo `5`. -/
theorem ray_partition_5 : (Finset.univ.filter (fun r : ZMod 5 => r ≠ 0)).card = 4 := by decide

end C3.BCon

