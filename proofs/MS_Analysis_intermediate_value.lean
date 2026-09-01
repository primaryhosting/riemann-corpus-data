import Mathlib
namespace MS.Analysis
theorem intermediate_value (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (y : ℝ) (hy : y ∈ Set.Icc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf hy
  exact ⟨c, hc, hfc⟩
theorem mean_value (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hc : ContinuousOn f (Set.Icc a b)) (hd : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hc hd
theorem extreme_value (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f c := by
  obtain ⟨c, hc, hmax⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_isMaxOn (Set.nonempty_Icc.2 hab) hf
  exact ⟨c, hc, fun x hx => hmax hx⟩
theorem bolzano_weierstrass (s : ℕ → ℝ) (M : ℝ) (hs : ∀ n, |s n| ≤ M) :
    ∃ (a : ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (s ∘ φ) Filter.atTop (nhds a) := by
  have hbdd : Bornology.IsBounded (Set.Icc (-M) M) := Metric.isBounded_Icc _ _
  have hmem : ∀ n, s n ∈ Set.Icc (-M) M := fun n => abs_le.1 (hs n)
  obtain ⟨a, -, φ, hφ, htend⟩ := tendsto_subseq_of_bounded hbdd hmem
  exact ⟨a, φ, hφ, htend⟩
theorem cantor_uncountable : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
end MS.Analysis

