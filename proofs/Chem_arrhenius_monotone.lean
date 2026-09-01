/-
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-Ea / (R * T))

/-- For a positive pre-exponential factor `A`, positive activation energy `Ea`,
positive gas constant `R`, the Arrhenius rate constant is strictly increasing in
the temperature `T` on the positive temperatures. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hlt : T₁ < T₂) :
    arrhenius A Ea R T₁ < arrhenius A Ea R T₂ := by
  have hT₂ : 0 < T₂ := hT₁.trans hlt
  have h1 : 0 < R * T₁ := mul_pos hR hT₁
  have h2 : 0 < R * T₂ := mul_pos hR hT₂
  have hmul : R * T₁ < R * T₂ := by nlinarith
  have hdiv : Ea / (R * T₂) < Ea / (R * T₁) :=
    div_lt_div_of_pos_left hEa h1 hmul
  have hexp : Real.exp (-Ea / (R * T₁)) < Real.exp (-Ea / (R * T₂)) := by
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_div]
    linarith
  exact mul_lt_mul_of_pos_left hexp hA

end Chem

