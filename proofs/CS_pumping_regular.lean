import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace CS

/-- **Pumping lemma for regular languages.**
Every regular language `L` admits a pumping length `p > 0`: every word `w ∈ L` of length at
least `p` can be split as `w = x ++ y ++ z` with `|x ++ y| ≤ p`, `y ≠ []`, and such that
`x ++ yⁿ ++ z ∈ L` for every `n : ℕ`. -/
theorem pumping_regular {α : Type*} (L : Language α) (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List α, w = x ++ y ++ z ∧ (x ++ y).length ≤ p ∧ y ≠ [] ∧
        ∀ n : ℕ, x ++ (List.replicate n y).flatten ++ z ∈ L := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  refine ⟨Fintype.card σ + 1, Nat.succ_pos _, ?_⟩
  intro w hw hlen
  obtain ⟨x, y, z, hsplit, hxy, hy, hpump⟩ :=
    M.pumping_lemma hw (le_trans (Nat.le_succ _) hlen)
  refine ⟨x, y, z, hsplit, ?_, hy, ?_⟩
  · simpa [List.length_append] using Nat.le_succ_of_le hxy
  · intro n
    have hkstar : (List.replicate n y).flatten ∈ KStar.kstar ({y} : Language α) :=
      Language.mem_kstar.2 ⟨List.replicate n y, rfl, fun t ht => List.eq_of_mem_replicate ht⟩
    have hmem : x ++ (List.replicate n y).flatten ∈ ({x} : Language α) * KStar.kstar {y} :=
      Language.mem_mul.2 ⟨x, rfl, _, hkstar, rfl⟩
    exact hpump (Language.mem_mul.2 ⟨_, hmem, z, rfl, by simp⟩)

end CS

