import Mathlib
namespace Brockian.MsCeva

/-- Auxiliary: for three non-collinear points `A B C` of the plane, the vectors `B - A` and
`C - A` are linearly independent (stated in the concrete "no nontrivial relation" form). -/
lemma indep_of_not_collinear {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (x y : ℝ) (hxy : x • (B - A) + y • (C - A) = 0) : x = 0 ∧ y = 0 := by
  by_cases hx : x = 0
  · refine ⟨hx, ?_⟩
    by_contra hy
    subst hx
    simp at hxy
    rcases hxy with hxy | hxy
    · exact absurd hxy hy
    · have hCA : C = A := sub_eq_zero.mp hxy
      subst hCA
      exact h (by simpa [Set.insert_comm, Set.pair_comm] using (collinear_pair ℝ C B))
  · exfalso
    apply h
    have hxy' : x * (-y / x) = -y := by field_simp
    have hB : B - A = (-y / x) • (C - A) := by
      refine smul_right_injective _ hx ?_
      show x • (B - A) = x • ((-y / x) • (C - A))
      rw [smul_smul, hxy']
      linear_combination (norm := module) hxy
    refine (collinear_iff_of_mem (Set.mem_insert A _)).2 ⟨C - A, ?_⟩
    rintro p (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨-y / x, by rw [← hB]; simp⟩
    · exact ⟨1, by simp⟩

/-- Auxiliary algebraic step (forward direction of Ceva). -/
lemma ceva_alg_forward {u v w s t r : ℝ}
    (e1 : s * (1 - u) = 1 - t) (e2 : s * u = t * (1 - v))
    (e3 : s * (1 - u) = r * w) (e4 : s * u = 1 - r) :
    u * v * w = (1 - u) * (1 - v) * (1 - w) := by
  linear_combination ((1 - u) + u * w) * e2 + ((1 - u) + u * w) * (1 - v) * e1
    - (u + (1 - u) * (1 - v)) * e3 - (u + (1 - u) * (1 - v)) * w * e4

/-- Auxiliary: if `s` is the parameter with `s * (u + (1-u)(1-v)) = 1 - v`, then the point of the
cevian `AD` with parameter `s` also lies on the cevian `BE`. -/
lemma ceva_pt_BE (A B C : EuclideanSpace ℝ (Fin 2)) (u v s : ℝ)
    (hs : s * (u + (1 - u) * (1 - v)) = 1 - v) :
    A + s • ((B + u • (C - B)) - A) = B + (1 - s * (1 - u)) • ((C + v • (A - C)) - B) := by
  match_scalars <;> first | linear_combination hs | linear_combination -hs | ring

/-- Auxiliary: if `s * (1-u) + s * u * w = w`, then the point of the cevian `AD` with parameter
`s` also lies on the cevian `CF`. -/
lemma ceva_pt_CF (A B C : EuclideanSpace ℝ (Fin 2)) (u w s : ℝ)
    (hs2 : s * (1 - u) + s * u * w = w) :
    A + s • ((B + u • (C - B)) - A) = C + (1 - s * u) • ((A + w • (B - A)) - C) := by
  match_scalars <;> first | linear_combination hs2 | linear_combination -hs2 | ring

/-- Ceva's theorem (ratio form): if D,E,F lie on segments BC,CA,AB with parameters splitting
    them in ratios giving points D=B+u(C−B), E=C+v(A−C), F=A+w(B−A), then the cevians AD,BE,CF
    are concurrent iff (u/(1−u))·(v/(1−v))·(w/(1−w)) = 1.

    Note: a non-degeneracy hypothesis (`A`, `B`, `C` not collinear) has been added; without it
    the statement is false (e.g. `A = B = C` makes the left-hand side trivially true). -/
theorem ceva (A B C : EuclideanSpace ℝ (Fin 2)) (u v w : ℝ)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) (hw : 0 < w ∧ w < 1)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (D E F : EuclideanSpace ℝ (Fin 2))
    (hD : D = B + u • (C - B)) (hE : E = C + v • (A - C)) (hF : F = A + w • (B - A)) :
    (∃ P : EuclideanSpace ℝ (Fin 2),
       (∃ s : ℝ, P = A + s • (D - A)) ∧ (∃ t : ℝ, P = B + t • (E - B)) ∧
       (∃ r : ℝ, P = C + r • (F - C)))
    ↔ (u / (1 - u)) * (v / (1 - v)) * (w / (1 - w)) = 1 := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  obtain ⟨hw0, hw1⟩ := hw
  have hu1' : (1 : ℝ) - u ≠ 0 := by linarith
  have hv1' : (1 : ℝ) - v ≠ 0 := by linarith
  have hw1' : (1 : ℝ) - w ≠ 0 := by linarith
  have hK : u + (1 - u) * (1 - v) ≠ 0 := by nlinarith
  have key : (∃ P : EuclideanSpace ℝ (Fin 2),
       (∃ s : ℝ, P = A + s • (D - A)) ∧ (∃ t : ℝ, P = B + t • (E - B)) ∧
       (∃ r : ℝ, P = C + r • (F - C)))
      ↔ u * v * w = (1 - u) * (1 - v) * (1 - w) := by
    constructor
    · rintro ⟨P, ⟨s, hs⟩, ⟨t, ht⟩, ⟨r, hr⟩⟩
      have h1 : (s * (1 - u) - (1 - t)) • (B - A) + (s * u - t * (1 - v)) • (C - A) = 0 := by
        subst hD hE hF
        linear_combination (norm := module) ht - hs
      have h2 : (s * (1 - u) - r * w) • (B - A) + (s * u - (1 - r)) • (C - A) = 0 := by
        subst hD hE hF
        linear_combination (norm := module) hr - hs
      obtain ⟨p1, p2⟩ := indep_of_not_collinear hABC _ _ h1
      obtain ⟨p3, p4⟩ := indep_of_not_collinear hABC _ _ h2
      exact ceva_alg_forward (s := s) (t := t) (r := r) (by linarith) (by linarith)
        (by linarith) (by linarith)
    · intro hprod
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s * (u + (1 - u) * (1 - v)) = 1 - v :=
        ⟨(1 - v) / (u + (1 - u) * (1 - v)), div_mul_cancel₀ _ hK⟩
      have hs2 : s * (1 - u) + s * u * w = w := by
        refine mul_left_cancel₀ hK ?_
        linear_combination ((1 - u) + u * w) * hs - hprod
      subst hD hE hF
      exact ⟨A + s • ((B + u • (C - B)) - A), ⟨s, rfl⟩,
        ⟨1 - s * (1 - u), ceva_pt_BE A B C u v s hs⟩,
        ⟨1 - s * u, ceva_pt_CF A B C u w s hs2⟩⟩
  rw [key]
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_one_iff_eq (by simp [hu1', hv1', hw1'])]

end Brockian.MsCeva

