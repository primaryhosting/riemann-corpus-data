import Mathlib
namespace Brockian.Schur

/-- Bound function for the Ramsey-type induction: `fR k` many integers suffice when the
    differences take at most `k` colours. -/
def fR : ℕ → ℕ
  | 0 => 2
  | (n + 1) => (n + 1) * fR n + 2

lemma fR_pos (k : ℕ) : 0 < fR k := by
  cases k <;> simp [fR]

/-- Ramsey-type core lemma: if `A` is a finite set of naturals with at least `fR k` elements,
    all of whose positive differences receive colours in a set `S` of size `k`, then `A`
    contains `a < b < d` with `c (b-a) = c (d-b) = c (d-a)`. -/
lemma key (r : ℕ) (c : ℕ → Fin r) :
    ∀ (k : ℕ) (S : Finset (Fin r)), S.card = k → ∀ A : Finset ℕ, fR k ≤ A.card →
      (∀ a ∈ A, ∀ b ∈ A, a < b → c (b - a) ∈ S) →
      ∃ a ∈ A, ∃ b ∈ A, ∃ d ∈ A, a < b ∧ b < d ∧
        c (b - a) = c (d - b) ∧ c (d - b) = c (d - a) := by
  intro k
  induction k with
  | zero =>
      intro S hS A hA hcol
      -- `S` is empty but `A` has at least two elements: contradiction.
      exfalso
      have hSe : S = ∅ := Finset.card_eq_zero.mp hS
      have h2 : 2 ≤ A.card := by simpa [fR] using hA
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
      rcases lt_or_gt_of_ne hab with h | h
      · have := hcol a ha b hb h; simp [hSe] at this
      · have := hcol b hb a ha h; simp [hSe] at this
  | succ k ih =>
      intro S hS A hA hcol
      set m := (k + 1) * fR k with hm
      have hA2 : m + 2 ≤ A.card := hA
      have hApos : A.Nonempty := by
        rw [← Finset.card_pos]; omega
      set a := A.min' hApos with ha_def
      have haA : a ∈ A := A.min'_mem hApos
      set A' := A.erase a with hA'_def
      have hlt : ∀ x ∈ A', a < x := by
        intro x hx
        exact lt_of_le_of_ne (A.min'_le x (Finset.mem_of_mem_erase hx))
          (Ne.symm (Finset.ne_of_mem_erase hx))
      have hA'card : S.card * fR k < A'.card := by
        rw [hA'_def, Finset.card_erase_of_mem haA, hS]
        omega
      have hmaps : ∀ x ∈ A', c (x - a) ∈ S := fun x hx =>
        hcol a haA x (Finset.mem_of_mem_erase hx) (hlt x hx)
      obtain ⟨s, hsS, hBcard⟩ :=
        Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hA'card
      set B := {x ∈ A' | c (x - a) = s} with hB_def
      have hBA' : B ⊆ A' := Finset.filter_subset _ _
      have hBA : B ⊆ A := fun x hx => Finset.mem_of_mem_erase (hBA' hx)
      have hBs : ∀ x ∈ B, c (x - a) = s := fun x hx => (Finset.mem_filter.mp hx).2
      by_cases hcase : ∃ b ∈ B, ∃ d ∈ B, b < d ∧ c (d - b) = s
      · obtain ⟨b, hb, d, hd, hbd, hcd⟩ := hcase
        exact ⟨a, haA, b, hBA hb, d, hBA hd, hlt b (hBA' hb), hbd,
          by rw [hBs b hb, hcd], by rw [hcd, hBs d hd]⟩
      · push_neg at hcase
        have hcol' : ∀ x ∈ B, ∀ y ∈ B, x < y → c (y - x) ∈ S.erase s := by
          intro x hx y hy hxy
          exact Finset.mem_erase.mpr ⟨hcase x hx y hy hxy, hcol x (hBA hx) y (hBA hy) hxy⟩
        obtain ⟨p, hp, q, hq, t, ht, h1, h2, h3, h4⟩ :=
          ih (S.erase s) (by rw [Finset.card_erase_of_mem hsS, hS]; omega) B (le_of_lt hBcard) hcol'
        exact ⟨p, hBA hp, q, hBA hq, t, hBA ht, h1, h2, h3, h4⟩

/-- Schur's theorem: for any finite coloring, some sufficiently large interval contains a
    monochromatic solution of x + y = z.

    (The hypothesis `0 < r` is part of the requested statement; the proof does not need it.) -/
theorem schur (r : ℕ) (hr : 0 < r) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : ℕ → Fin r,
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≤ N ∧ y ≤ N ∧ z ≤ N ∧
        x + y = z ∧ c x = c y ∧ c y = c z := by
  refine ⟨fR r, fR_pos r, ?_⟩
  intro c
  obtain ⟨a, ha, b, hb, d, hd, hab, hbd, h1, h2⟩ :=
    key r c r Finset.univ (by simp) (Finset.range (fR r)) (by simp)
      (fun a _ b _ _ => Finset.mem_univ _)
  simp only [Finset.mem_range] at ha hb hd
  refine ⟨b - a, d - b, d - a, by omega, by omega, by omega, by omega, by omega, by omega, h1, h2⟩

end Brockian.Schur

