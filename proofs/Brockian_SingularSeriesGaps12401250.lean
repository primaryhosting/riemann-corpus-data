import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace Brockian

/-- A gap `h` is *admissible* when the pair `{0, h}` is an admissible 2-tuple in the
Hardy–Littlewood sense: for every prime `p`, the reductions of `0` and `h` modulo `p`
do not cover all residue classes mod `p`.  This is exactly the condition under which the
singular series `𝔖(h)` attached to the gap `h` is nonzero. -/
def AdmissibleGap (h : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (({0, h} : Finset ℕ).image (· % p)).card < p

/-- A gap `h` is admissible exactly when it is even (the only obstruction comes from `p = 2`). -/
theorem admissibleGap_iff_even (h : ℕ) : AdmissibleGap h ↔ Even h := by
  constructor
  · intro hadm
    have h2 := hadm 2 Nat.prime_two
    rw [Nat.even_iff]
    by_contra hodd
    have h1 : h % 2 = 1 := Nat.mod_two_ne_zero.mp hodd
    have himg : (({0, h} : Finset ℕ).image (· % 2)) = {0, 1} := by
      ext x; simp [h1]
    rw [himg] at h2
    simp at h2
  · intro he p hp
    rcases eq_or_ne p 2 with rfl | hne
    · have h0 : h % 2 = 0 := Nat.even_iff.mp he
      have himg : (({0, h} : Finset ℕ).image (· % 2)) = {0} := by
        ext x; simp [h0]
      rw [himg]; simp
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      calc (({0, h} : Finset ℕ).image (· % p)).card ≤ ({0, h} : Finset ℕ).card :=
            Finset.card_image_le
        _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
        _ < p := by omega

/-- **Singular series gaps in the range `1240 ≤ h ≤ 1250`.**
Within this gap range, a gap is admissible precisely when it is even; consequently exactly
six of the eleven gaps in the range are admissible, namely
`1240, 1242, 1244, 1246, 1248, 1250`, while the odd gaps `1241, …, 1249` are inadmissible. -/
theorem SingularSeriesGaps12401250 :
    (∀ h ∈ Finset.Icc 1240 1250, (AdmissibleGap h ↔ Even h)) ∧
    (Finset.Icc 1240 1250).filter (fun h => AdmissibleGap h) = {1240, 1242, 1244, 1246, 1248, 1250} ∧
    ((Finset.Icc 1240 1250).filter (fun h => AdmissibleGap h)).card = 6 := by
  have hfilter :
      (Finset.Icc 1240 1250).filter (fun h => AdmissibleGap h)
        = (Finset.Icc 1240 1250).filter (fun h => Even h) := by
    apply Finset.filter_congr
    intro h _
    simpa using admissibleGap_iff_even h
  have hset : (Finset.Icc 1240 1250).filter (fun h => Even h)
      = ({1240, 1242, 1244, 1246, 1248, 1250} : Finset ℕ) := by decide
  refine ⟨fun h _ => admissibleGap_iff_even h, ?_, ?_⟩
  · rw [hfilter, hset]
  · rw [hfilter, hset]; decide

end Brockian

#print axioms Brockian.SingularSeriesGaps12401250

