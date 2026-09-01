import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The one-loop coefficient `b₀` of the SU(N) gauge beta function with `nf` Dirac
fermion flavours in the fundamental representation:
`b₀ = 11 N / 3 - 2 nf / 3`. -/
noncomputable def b0 (N nf : ℕ) : ℝ := 11 * (N : ℝ) / 3 - 2 * (nf : ℝ) / 3

/-- The one-loop beta function of the SU(N) gauge coupling:
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N nf : ℕ) (g : ℝ) : ℝ :=
  -(b0 N nf) * g ^ 3 / (16 * Real.pi ^ 2)

/-- **Asymptotic freedom (one loop).** For an SU(N) gauge theory with `nf` fermion
flavours in the fundamental representation, if the number of flavours is small enough
(`2 nf < 11 N`, i.e. `b₀ > 0`) and the coupling is positive, then the one-loop beta
function is strictly negative: the coupling decreases towards the UV. -/
theorem asymptotic_freedom_sign (N nf : ℕ) (g : ℝ) (hg : 0 < g)
    (hflav : 2 * nf < 11 * N) : betaOneLoop N nf g < 0 := by
  have hb : 0 < b0 N nf := by
    have : (2 : ℝ) * (nf : ℝ) < 11 * (N : ℝ) := by exact_mod_cast hflav
    unfold b0
    linarith
  have hpi : 0 < 16 * Real.pi ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hpi
  nlinarith

/-- Pure Yang–Mills (`nf = 0`) with `N ≥ 1` is asymptotically free. -/
theorem asymptotic_freedom_pure_gauge (N : ℕ) (hN : 1 ≤ N) (g : ℝ) (hg : 0 < g) :
    betaOneLoop N 0 g < 0 :=
  asymptotic_freedom_sign N 0 g hg (by omega)

end Frontier

