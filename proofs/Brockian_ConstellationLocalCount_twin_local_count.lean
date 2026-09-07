import Mathlib

/-
# Constellation Sieve Spectrum — Brick 1: local admissibility count.

For a modulus `n` and a finite offset set `H : Finset ℤ` (a "prime constellation"
pattern), a residue `a : ZMod n` is *admissible* when none of the shifted points
`a + h` hits `0` in `ZMod n`, i.e. `∀ h ∈ H, a + (h : ZMod n) ≠ 0`.

This file establishes the exact count of admissible residues:

    #{admissible a} = |ZMod n| − ν,     where  ν = |{ (h : ZMod n) : h ∈ H }|,

the number of DISTINCT residues of `H` mod `n`. The proof identifies the forbidden
set `F = { -(h : ZMod n) : h ∈ H }` (the exact complement of the admissible set) and
uses that negation is injective, so `|F| = ν`.

`local_admissible_count`        — general modulus `n` (`[NeZero n]`), the brick.
`local_admissible_count_prime`  — specialization to a prime `p`, giving `p − ν`.
`twin_local_count`              — twin constellation `H = {0,2}` at a prime `p ≥ 3`:
                                   exactly `p − 2` admissible residues (confinement).

No `sorry`, `admit`, `native_decide`, or `axiom` is used. Core Mathlib only.
-/

namespace Brockian.ConstellationLocalCount

/-- **Brick 1 (general modulus).** The number of admissible residues mod `n` for the
constellation `H` equals `|ZMod n|` minus the number `ν` of distinct residues of `H`
mod `n`. A residue `a` is admissible iff `a + h ≠ 0` for every `h ∈ H`. -/
theorem local_admissible_count (n : ℕ) [NeZero n] (H : Finset ℤ) :
    (Finset.univ.filter (fun a : ZMod n => ∀ h ∈ H, a + (h : ZMod n) ≠ 0)).card
      = Fintype.card (ZMod n) - (H.image (fun h : ℤ => (h : ZMod n))).card := by
  classical
  -- Step 1: the admissible set is exactly the complement of the forbidden set
  -- `F = { -(h : ZMod n) : h ∈ H }`, since `a + h = 0 ↔ a = -h`.
  have hset : (Finset.univ.filter (fun a : ZMod n => ∀ h ∈ H, a + (h : ZMod n) ≠ 0))
      = Finset.univ \ (H.image (fun h : ℤ => -(h : ZMod n))) := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ a, ?_⟩
      rw [Finset.mem_image]
      rintro ⟨h, hh, hEq⟩
      exact ha.2 h hh (by rw [← hEq]; ring)
    · intro ha
      rw [Finset.mem_sdiff, Finset.mem_image] at ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ a, ?_⟩
      intro h hh hEq
      exact ha.2 ⟨h, hh, neg_eq_of_add_eq_zero_left hEq⟩
  rw [hset, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  -- Step 2: `|F| = ν` because negation is injective.
  congr 1
  have himg : (H.image (fun h : ℤ => -(h : ZMod n)))
      = (H.image (fun h : ℤ => (h : ZMod n))).image (fun x => -x) := by
    rw [Finset.image_image]; rfl
  rw [himg, Finset.card_image_of_injective _ neg_injective]

/-- **Brick 1 at a prime.** For a prime `p`, the number of admissible residues mod `p`
for the constellation `H` equals `p` minus the number of distinct residues of `H`. -/
theorem local_admissible_count_prime (p : ℕ) [Fact p.Prime] (H : Finset ℤ) :
    (Finset.univ.filter (fun a : ZMod p => ∀ h ∈ H, a + (h : ZMod p) ≠ 0)).card
      = p - (H.image (fun h : ℤ => (h : ZMod p))).card := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [local_admissible_count p H, ZMod.card p]

/-- **Twin constellation confinement.** For a prime `p ≥ 3`, the twin pattern
`H = {0, 2}` admits exactly `p − 2` residues: precisely those `a` with `a ≠ 0` and
`a + 2 ≠ 0`. -/
theorem twin_local_count (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a + 2 ≠ 0)).card = p - 2 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  -- The forbidden residues `{0, 2}` mod `p` are distinct when `p ≥ 3`, so `ν = 2`.
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact hc
    rw [CharP.cast_eq_zero_iff (ZMod p) p 2] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hne : ((0 : ℤ) : ZMod p) ≠ ((2 : ℤ) : ZMod p) := by
    intro hc
    push_cast at hc
    exact h2ne hc.symm
  have himg : (({0, 2} : Finset ℤ).image (fun h : ℤ => (h : ZMod p))).card = 2 := by
    rw [Finset.image_insert, Finset.image_singleton,
        Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
  -- Brick 2 for `H = {0,2}` gives count `p - ν = p - 2`; connect via `hfilter`.
  have key := local_admissible_count_prime p ({0, 2} : Finset ℤ)
  rw [himg] at key
  rw [← key]
  -- Reduce to: the twin filter equals the `{0,2}`-constellation filter.
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h0, h2⟩ h (rfl | rfl)
    · simpa using h0
    · simpa using h2
  · intro h
    exact ⟨by simpa using h 0 (Or.inl rfl), by simpa using h 2 (Or.inr rfl)⟩

end Brockian.ConstellationLocalCount
