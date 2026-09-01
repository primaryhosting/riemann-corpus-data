import Mathlib

/-!
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace Math

/-- **Inclusion–exclusion principle**.

For a finite index set `s` and a family of finite sets `S i`, the cardinality of the union
`⋃ i ∈ s, S i` equals the alternating sum over all nonempty subsets `t ⊆ s` of
`(-1) ^ (|t| + 1) * |⋂ i ∈ t, S i|`.

Here the intersection `⋂ i ∈ t, S i` is realized as the elements of the union that lie in every
`S i` for `i ∈ t` (which, for nonempty `t ⊆ s`, is exactly the intersection).

This is derived from `Finset.inclusion_exclusion_card_biUnion` in Mathlib. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α] (s : Finset ι) (S : ι → Finset α) :
    (#(s.biUnion S) : ℤ) = ∑ t ∈ s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t + 1) * #((s.biUnion S).filter (fun a => ∀ i ∈ t, a ∈ S i)) := by
  rw [Finset.inclusion_exclusion_card_biUnion s S,
    ← Finset.sum_attach (s.powerset.filter (·.Nonempty))
      (fun t => (-1 : ℤ) ^ (#t + 1) * #((s.biUnion S).filter (fun a => ∀ i ∈ t, a ∈ S i)))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨t, ht⟩ -
  have ht' := Finset.mem_filter.1 ht
  have hne : t.Nonempty := ht'.2
  have hsub : t ⊆ s := Finset.mem_powerset.1 ht'.1
  have hEq : t.inf' hne S = (s.biUnion S).filter (fun a => ∀ i ∈ t, a ∈ S i) := by
    ext a
    simp only [Finset.mem_inf', Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := hne
      exact ⟨⟨i, hsub hi, h i hi⟩, h⟩
    · exact fun h => h.2
  simp only [hEq]

end Math

#print axioms Math.inclusion_exclusion

