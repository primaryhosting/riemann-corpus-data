import Mathlib
open Filter Topology
namespace MS2.Analysis2

theorem squeeze (f g h : ℕ → ℝ) (a : ℝ) (hf : Tendsto f atTop (nhds a)) (hh : Tendsto h atTop (nhds a))
    (hfg : ∀ n, f n ≤ g n) (hgh : ∀ n, g n ≤ h n) : Tendsto g atTop (nhds a) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh hfg hgh

theorem geometric_sum (r : ℝ) (hr : |r| < 1) : Tendsto (fun n => ∑ i ∈ Finset.range n, r^i) atTop (nhds (1/(1-r))) := by
  have h := (hasSum_geometric_of_abs_lt_one hr).tendsto_sum_nat
  simpa [one_div] using h

theorem monotone_bounded_converges (s : ℕ → ℝ) (hm : Monotone s) (M : ℝ) (hb : ∀ n, s n ≤ M) :
    ∃ L, Tendsto s atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciSup hm ⟨M, by rintro _ ⟨n, rfl⟩; exact hb n⟩⟩

/-- Rolle's theorem. The differentiability hypothesis `hd` is not needed for this
conclusion (Mathlib's `exists_deriv_eq_zero` only requires continuity: at a point where
`f` is not differentiable, `deriv f` is defined to be `0`), but it is kept as it was
part of the requested statement. -/
theorem rolle (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hc : ContinuousOn f (Set.Icc a b))
    (hd : DifferentiableOn ℝ f (Set.Ioo a b)) (he : f a = f b) : ∃ c ∈ Set.Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hc he

theorem harmonic_diverges : ¬ ∃ L, Tendsto (fun n => ∑ i ∈ Finset.range n, (1:ℝ)/(i+1)) atTop (nhds L) := by
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop L hL

end MS2.Analysis2

