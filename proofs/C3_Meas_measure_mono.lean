import Mathlib
open MeasureTheory
namespace C3.Meas
theorem measure_mono {X : Type*} [MeasurableSpace X] (μ : Measure X) {s t : Set X} (h : s ⊆ t) : μ s ≤ μ t :=
  MeasureTheory.measure_mono h
theorem measure_union_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (s t : Set X) : μ (s ∪ t) ≤ μ s + μ t :=
  MeasureTheory.measure_union_le s t
theorem integral_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x ∂μ :=
  MeasureTheory.integral_nonneg hf
end C3.Meas

