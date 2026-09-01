import Mathlib
open intervalIntegral MeasureTheory
namespace C2.An4

/-- Fundamental theorem of calculus: if `F` has derivative `f` everywhere and `f` is
continuous, then `∫ x in a..b, f x = F b - F a`. -/
theorem ftc (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ x, HasDerivAt F (f x) x) (hc : Continuous f) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hc.intervalIntegrable a b)

/-- The partial sums of a geometric series with ratio `|r| < 1` converge to `1 / (1 - r)`. -/
theorem geom_series_sum (r : ℝ) (hr : |r| < 1) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, r ^ i) Filter.atTop (nhds (1 / (1 - r))) := by
  rw [one_div]
  exact (hasSum_geometric_of_abs_lt_one hr).tendsto_sum_nat

/-- A function continuous on the compact interval `[a, b]` is uniformly continuous there. -/
theorem uniform_cont_on_compact (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    UniformContinuousOn f (Set.Icc a b) :=
  isCompact_Icc.uniformContinuousOn_of_continuous hf

end C2.An4

