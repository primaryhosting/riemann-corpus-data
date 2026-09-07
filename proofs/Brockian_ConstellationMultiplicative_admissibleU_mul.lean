import Mathlib
import Brockian.ConstellationLocalCount

/-
# Constellation Sieve Spectrum — Brick 2: wheel admissibility is MULTIPLICATIVE (CRT).

Brick 1 (`Brockian/ConstellationLocalCount.lean`) counted, at a modulus `n`, the residues
that dodge `0` under a constellation `H`. The genuine sieve/wheel condition is stronger: a
residue survives the wheel of modulus `n` iff every shifted point `a + h` is a *unit* of
`ZMod n` (coprime to `n`), not merely nonzero. Write

    admissibleU n H = { a : ZMod n | ∀ h ∈ H, IsUnit (a + h) }.

This brick establishes the two structural facts that turn local data into the wheel product
`∏_{p} (p − ν_p)`:

`admissibleU_prime`  — **prime bridge.** In a field `ZMod p`, `IsUnit x ↔ x ≠ 0`, so the wheel
                       condition collapses to Brick 1's "dodge `0`" condition; the count is
                       exactly `p − ν`, `ν = |H mod p|`. This is the base of the wheel product.

`admissibleU_mul`    — **multiplicativity (CRT).** For coprime moduli `m, n`, the wheel
                       admissibility count is multiplicative:
                           |admissibleU (m·n) H| = |admissibleU m H| · |admissibleU n H|.
                       Proof: the ring isomorphism `ZMod.chineseRemainder : ZMod (m·n) ≃+*
                       ZMod m × ZMod n` carries the offset `a + h` componentwise to
                       `((e a).1 + h, (e a).2 + h)`; a unit in a product is a pair of units
                       (`Prod.isUnit_iff`) and a ring equiv preserves `IsUnit`, so the
                       composite admissible set is the CRT image of the product of the local
                       admissible sets. Cardinality multiplies via `Finset.card_product`.

Composing the two across the primes dividing a wheel modulus yields the wheel product
`∏_p (p − ν_p)` from Brick 1's per-prime local counts.

No `sorry`, `admit`, `native_decide`, or `axiom` is used. Core Mathlib only.
-/

namespace Brockian.ConstellationMultiplicative

open Classical in
/-- **Wheel admissibility.** The residues `a : ZMod n` for which every shifted constellation
point `a + h` (`h ∈ H`) is a *unit* of `ZMod n`, i.e. coprime to the modulus. This is the
genuine wheel/sieve survival condition (stronger than merely avoiding `0`). -/
noncomputable def admissibleU (n : ℕ) [NeZero n] (H : Finset ℤ) : Finset (ZMod n) :=
  Finset.univ.filter (fun a => ∀ h ∈ H, IsUnit (a + (h : ZMod n)))

/-- **Brick 2 prime bridge.** For a prime `p`, `ZMod p` is a field, where `IsUnit x ↔ x ≠ 0`.
Thus wheel admissibility coincides with Brick 1's "avoid `0`" admissibility, and the count is
`p − ν`, where `ν = |{ (h : ZMod p) : h ∈ H }|`. This anchors the wheel product at each prime. -/
theorem admissibleU_prime (p : ℕ) [Fact p.Prime] (H : Finset ℤ) :
    (admissibleU p H).card = p - (H.image (fun h : ℤ => (h : ZMod p))).card := by
  classical
  rw [← Brockian.ConstellationLocalCount.local_admissible_count_prime p H]
  congr 1
  unfold admissibleU
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hu h hh
    exact isUnit_iff_ne_zero.mp (hu h hh)
  · intro hz h hh
    exact isUnit_iff_ne_zero.mpr (hz h hh)

/-- **Brick 2 multiplicativity (CRT).** For coprime moduli `m, n`, wheel admissibility is
multiplicative across the product modulus:

    |admissibleU (m · n) H| = |admissibleU m H| · |admissibleU n H|.

The Chinese Remainder ring isomorphism `e = ZMod.chineseRemainder h` carries the constellation
offset componentwise, a product-ring unit is a pair of units, and `e` preserves `IsUnit`; hence
the composite admissible set is the `e`-image of the product of the local admissible sets, whose
cardinality is the product `|A_m| · |A_n|`. This is the multiplicative engine of the wheel. -/
theorem admissibleU_mul {m n : ℕ} [NeZero m] [NeZero n] (h : Nat.Coprime m n) (H : Finset ℤ) :
    (admissibleU (m * n) H).card = (admissibleU m H).card * (admissibleU n H).card := by
  classical
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set e := ZMod.chineseRemainder h with he
  -- A ring equiv preserves `IsUnit` (both directions).
  have eiff : ∀ x : ZMod (m * n), IsUnit x ↔ IsUnit (e x) := by
    intro x
    refine ⟨fun hx => hx.map e, fun hx => ?_⟩
    have hx' := hx.map e.symm
    rwa [e.symm_apply_apply] at hx'
  -- `e` sends the offset `a + b` componentwise to `((e a).1 + b, (e a).2 + b)`.
  have hc1 : ∀ (a : ZMod (m * n)) (b : ℤ),
      (e (a + (b : ZMod (m * n)))).1 = (e a).1 + (b : ZMod m) := by
    intro a b
    rw [map_add, map_intCast]
    simp
  have hc2 : ∀ (a : ZMod (m * n)) (b : ℤ),
      (e (a + (b : ZMod (m * n)))).2 = (e a).2 + (b : ZMod n) := by
    intro a b
    rw [map_add, map_intCast]
    simp
  -- Per-point: `a + b` is a unit iff both CRT components `(e a).i + b` are units.
  have hh_iff : ∀ (a : ZMod (m * n)) (b : ℤ),
      IsUnit (a + (b : ZMod (m * n)))
        ↔ IsUnit ((e a).1 + (b : ZMod m)) ∧ IsUnit ((e a).2 + (b : ZMod n)) := by
    intro a b
    rw [eiff, Prod.isUnit_iff, hc1, hc2]
  -- Membership: `a` admissible over the product iff both CRT components are locally admissible.
  have mem_iff : ∀ a : ZMod (m * n),
      a ∈ admissibleU (m * n) H
        ↔ (e a).1 ∈ admissibleU m H ∧ (e a).2 ∈ admissibleU n H := by
    intro a
    unfold admissibleU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      exact ⟨fun b hb => ((hh_iff a b).mp (ha b hb)).1,
             fun b hb => ((hh_iff a b).mp (ha b hb)).2⟩
    · rintro ⟨h1, h2⟩ b hb
      exact (hh_iff a b).mpr ⟨h1 b hb, h2 b hb⟩
  -- The composite admissible set is the `e.symm`-image of the product of local sets.
  have hset : admissibleU (m * n) H
      = (admissibleU m H ×ˢ admissibleU n H).image (fun p => e.symm p) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_product]
    rw [mem_iff a]
    constructor
    · intro ha
      exact ⟨e a, ⟨ha.1, ha.2⟩, e.symm_apply_apply a⟩
    · rintro ⟨b, hb, hba⟩
      have hea : e a = b := by rw [← hba, e.apply_symm_apply]
      rw [hea]; exact ⟨hb.1, hb.2⟩
  rw [hset, Finset.card_image_of_injective _ e.symm.injective, Finset.card_product]

end Brockian.ConstellationMultiplicative
