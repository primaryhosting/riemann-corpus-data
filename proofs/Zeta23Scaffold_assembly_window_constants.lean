/-
# Assembly Window Constants
Category: A Assembly
Target: Zeta23Scaffold.assembly_window_constants
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

/-- The window function `H(λ) = 2 - 1/λ - λ/3`. -/
noncomputable def Hwin (lam : ℝ) : ℝ := 2 - 1 / lam - lam / 3

/-- The averaged window `H_d(λ) = (1 + H(λ))/2`. -/
noncomputable def Hd (lam : ℝ) : ℝ := (1 + Hwin lam) / 2

/-- The window function `F(λ) = λ / (1 + λ²/3)`. -/
noncomputable def Fwin (lam : ℝ) : ℝ := lam / (1 + lam ^ 2 / 3)

/-- Window-constant assembly identities of preprint eq. (1.3):
`H(1) = 2/3`, `H_d(1) = 5/6`, `F(1) = 3/4`, `2 F(1) - 1 = 1/2`. -/
theorem assembly_window_constants :
    Hwin 1 = 2 / 3 ∧ Hd 1 = 5 / 6 ∧ Fwin 1 = 3 / 4 ∧ 2 * Fwin 1 - 1 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Hwin, Hd, Fwin] <;> norm_num

end Zeta23Scaffold

