import Brockian.RiemannScaffold

namespace Brockian.RiemannXiFunctionalEquation

open Complex

/-!
## Riemann xi functional equation

Mathlib 4.32 already proves the completed zeta symmetry
`completedRiemannZeta_one_sub`.  Since the Brockian xi normalization is
`riemannXi s = s * (s - 1) * completedRiemannZeta s`, the classical xi
functional equation is the remaining polynomial identity.
-/

/-- The completed-zeta functional equation, restated at the Brockian import boundary. -/
theorem completedRiemannZeta_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- The Brockian Riemann xi function satisfies the classical symmetry `s ↦ 1 - s`. -/
theorem riemannXi_one_sub (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = RiemannScaffold.riemannXi s := by
  unfold RiemannScaffold.riemannXi
  rw [completedRiemannZeta_one_sub]
  ring

/-- The xi zero set is stable under `s ↦ 1 - s`. -/
theorem riemannXi_one_sub_eq_zero {s : ℂ} (h : RiemannScaffold.riemannXi s = 0) :
    RiemannScaffold.riemannXi (1 - s) = 0 := by
  rw [riemannXi_one_sub, h]

/-- Equivalent zero-set form of the xi functional equation. -/
theorem riemannXi_one_sub_eq_zero_iff (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = 0 ↔ RiemannScaffold.riemannXi s = 0 := by
  rw [riemannXi_one_sub]

end Brockian.RiemannXiFunctionalEquation
