import Mathlib
namespace Brockian.MsBeatty

/-- Hölder conjugacy from the hypotheses `1 < r` and `1/r + 1/s = 1`. -/
private lemma holderConj_of {r s : ℝ} (hr : 1 < r) (hsum : 1 / r + 1 / s = 1) :
    r.HolderConjugate s := by
  rw [Real.holderConjugate_iff]
  exact ⟨hr, by simpa [one_div] using hsum⟩

/-- Membership in the positive Beatty set, expressed with natural-number indices. -/
private lemma mem_beatty_iff (t : ℝ) (n : ℤ) :
    n ∈ {beattySeq t k | k > 0} ↔ ∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * t⌋ = n := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.toNat, by omega, ?_⟩
    have h : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
    rw [h]; rfl
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(m : ℤ), by exact_mod_cast hm, by simp [beattySeq]⟩

/-- Rayleigh–Beatty theorem: if 1/r + 1/s = 1 with r > 1 irrational, the Beatty sequences ⌊n·r⌋
    and ⌊n·s⌋ partition the positive integers — each n > 0 is hit by exactly one. -/
theorem beatty (r s : ℝ) (hr : 1 < r) (hirr : Irrational r) (hsum : 1 / r + 1 / s = 1)
    (n : ℕ) (hn : 0 < n) :
    (∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * r⌋ = (n : ℤ)) ↔
      ¬ (∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * s⌋ = (n : ℤ)) := by
  have hrs : r.HolderConjugate s := holderConj_of hr hsum
  have key := hirr.beattySeq_symmDiff_beattySeq_pos hrs
  have hmem : ((n : ℤ)) ∈ ({m | 0 < m} : Set ℤ) := by
    simpa using (Int.natCast_pos.2 hn)
  rw [← key, Set.mem_symmDiff, mem_beatty_iff, mem_beatty_iff] at hmem
  exact ⟨fun h ↦ hmem.elim (·.2) (fun x ↦ absurd h x.2),
    fun h ↦ hmem.elim (·.1) (fun x ↦ absurd x.1 h)⟩

end Brockian.MsBeatty

