import Mathlib
open Filter Topology
namespace C3.RA6

/-- The sum of two continuous real functions is continuous. -/
theorem cont_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) : Continuous (f + g) :=
  hf.add hg

/-- The product of two continuous real functions is continuous. -/
theorem cont_mul {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) : Continuous (f * g) :=
  hf.mul hg

/-- The derivative of a sum is the sum of the derivatives. -/
theorem deriv_add (f g : ℝ → ℝ) (x : ℝ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  _root_.deriv_add hf hg

end C3.RA6

