import Mathlib

/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Chem

/-- The van 't Hoff equilibrium constant as a function of absolute temperature `T`:
`K T = A * exp (-ΔH / (R * T))`, obtained by integrating the van 't Hoff equation
`d (log K) / dT = ΔH / (R * T ^ 2)` with `ΔH` and `R` constant. -/
noncomputable def K (A R dH T : ℝ) : ℝ := A * Real.exp (-dH / (R * T))

/-- **Le Chatelier sign (van 't Hoff).** For an exothermic reaction (`ΔH < 0`), with positive
pre-exponential factor `A` and positive gas constant `R`, the equilibrium constant
`K T = A * exp (-ΔH / (R * T))` is strictly decreasing in the absolute temperature `T > 0`. -/
theorem leChatelier_sign {A R dH : ℝ} (hA : 0 < A) (hR : 0 < R) (hdH : dH < 0) :
    StrictAntiOn (K A R dH) (Set.Ioi (0 : ℝ)) := by
  intro T₁ hT₁ T₂ hT₂ h12
  have hT₁' : (0:ℝ) < T₁ := Set.mem_Ioi.mp hT₁
  have hT₂' : (0:ℝ) < T₂ := Set.mem_Ioi.mp hT₂
  have hexp : -dH / (R * T₂) < -dH / (R * T₁) :=
    div_lt_div_of_pos_left (by linarith) (by positivity) (by nlinarith)
  have := Real.exp_lt_exp.mpr hexp
  simpa [K] using (mul_lt_mul_of_pos_left this hA)

end Chem

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

