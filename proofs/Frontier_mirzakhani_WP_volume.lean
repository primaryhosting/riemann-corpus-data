import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-! ## Weil–Petersson volume polynomials for small `(g, n)`

`V g n (b₁, …, bₙ)` denotes the Weil–Petersson volume of the moduli space
`M_{g,n}(b₁,…,bₙ)` of bordered hyperbolic surfaces of genus `g` with `n` geodesic
boundary components of lengths `b₁,…,bₙ`.  By Mirzakhani's theorem it is a
polynomial in `b₁²,…,bₙ²`.  We record the first few, as functions of complex
arguments (so that the boundary lengths may be analytically continued, as is
needed for the string and dilaton equations, where one substitutes `bₙ = 2πi`). -/

/-- `V_{0,3} = 1` (the pair of pants has WP volume 1). -/
noncomputable def V03 : ℂ := 1

/-- `V_{1,1}(b) = (b² + 4π²)/48`. -/
noncomputable def V11 (b : ℂ) : ℂ := (b ^ 2 + 4 * (Real.pi : ℂ) ^ 2) / 48

/-- `V_{0,4}(b₁,b₂,b₃,b₄) = (b₁² + b₂² + b₃² + b₄² + 4π²)/2`. -/
noncomputable def V04 (b₁ b₂ b₃ b₄ : ℂ) : ℂ :=
  (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + b₄ ^ 2 + 4 * (Real.pi : ℂ) ^ 2) / 2

/-- `V_{1,2}(b₁,b₂) = (4π² + b₁² + b₂²)(12π² + b₁² + b₂²)/192`. -/
noncomputable def V12 (b₁ b₂ : ℂ) : ℂ :=
  (4 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2 + b₂ ^ 2) * (12 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2 + b₂ ^ 2) / 192

/-! ## Mirzakhani's integration kernels

Mirzakhani's recursion for the volumes `V_{g,n}` is an integral recursion whose
integrands are built from the kernels `H`, `D` and `R` below. -/

/-- Mirzakhani's kernel `H(x, y) = 1/(1 + e^{(x+y)/2}) + 1/(1 + e^{(x-y)/2})`. -/
noncomputable def Hker (x y : ℝ) : ℝ :=
  1 / (1 + Real.exp ((x + y) / 2)) + 1 / (1 + Real.exp ((x - y) / 2))

/-- Mirzakhani's kernel
`D(x, y, z) = 2 log ((e^{x/2} + e^{(y+z)/2}) / (e^{-x/2} + e^{(y+z)/2}))`. -/
noncomputable def Dker (x y z : ℝ) : ℝ :=
  2 * Real.log ((Real.exp (x / 2) + Real.exp ((y + z) / 2)) /
    (Real.exp (-x / 2) + Real.exp ((y + z) / 2)))

/-- The kernel `D` written as a difference of logarithms. -/
lemma Dker_eq (x y z : ℝ) :
    Dker x y z = 2 * (Real.log (Real.exp (x / 2) + Real.exp ((y + z) / 2)) -
      Real.log (Real.exp (-x / 2) + Real.exp ((y + z) / 2))) := by
  have h₁ : Real.exp (x / 2) + Real.exp ((y + z) / 2) ≠ 0 := by positivity
  have h₂ : Real.exp (-x / 2) + Real.exp ((y + z) / 2) ≠ 0 := by positivity
  rw [Dker, Real.log_div h₁ h₂]

/-- **Mirzakhani's kernel identity**: `∂D/∂x (x, y, z) = H(y + z, x)`.
This is the analytic ingredient which turns Mirzakhani's integration-over-moduli
identity into her recursion for the volume polynomials. -/
lemma hasDerivAt_Dker (x y z : ℝ) :
    HasDerivAt (fun t : ℝ => Dker t y z) (Hker (y + z) x) x := by
  have hfun : (fun t : ℝ => Dker t y z) =
      fun t : ℝ => 2 * (Real.log (Real.exp (t / 2) + Real.exp ((y + z) / 2)) -
        Real.log (Real.exp (-t / 2) + Real.exp ((y + z) / 2))) := funext fun t => Dker_eq t y z
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (x / 2) * (1 / 2)) x := by
    simpa using ((hasDerivAt_id x).div_const 2).exp
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-x / 2) * (-1 / 2)) x := by
    simpa using (((hasDerivAt_id x).neg).div_const 2).exp
  have hne1 : Real.exp (x / 2) + Real.exp ((y + z) / 2) ≠ 0 := by positivity
  have hne2 : Real.exp (-x / 2) + Real.exp ((y + z) / 2) ≠ 0 := by positivity
  have g1 := (h1.add_const (Real.exp ((y + z) / 2))).log hne1
  have g2 := (h2.add_const (Real.exp ((y + z) / 2))).log hne2
  have hd := (g1.sub g2).const_mul (2 : ℝ)
  convert hd using 1
  have p1 : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have p2 : (0 : ℝ) < Real.exp (-x / 2) := Real.exp_pos _
  have pu : (0 : ℝ) < Real.exp ((y + z) / 2) := Real.exp_pos _
  have A : Real.exp (x / 2) / (Real.exp (x / 2) + Real.exp ((y + z) / 2))
      = 1 / (1 + Real.exp (((y + z) - x) / 2)) := by
    have h : Real.exp (x / 2) * Real.exp (((y + z) - x) / 2) = Real.exp ((y + z) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hd' : (0 : ℝ) < 1 + Real.exp (((y + z) - x) / 2) := by positivity
    field_simp
    linarith [h]
  have B : Real.exp (-x / 2) / (Real.exp (-x / 2) + Real.exp ((y + z) / 2))
      = 1 / (1 + Real.exp (((y + z) + x) / 2)) := by
    have h : Real.exp (-(x / 2)) * Real.exp (((y + z) + x) / 2) = Real.exp ((y + z) / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hd' : (0 : ℝ) < 1 + Real.exp (((y + z) + x) / 2) := by positivity
    field_simp
    linarith [h]
  rw [Hker, ← A, ← B]
  field_simp
  ring

/-- Mirzakhani's kernel
`R(x, y, z) = x - log ((cosh(y/2) + cosh((x+z)/2)) / (cosh(y/2) + cosh((x-z)/2)))`. -/
noncomputable def Rker (x y z : ℝ) : ℝ :=
  x - Real.log ((Real.cosh (y / 2) + Real.cosh ((x + z) / 2)) /
    (Real.cosh (y / 2) + Real.cosh ((x - z) / 2)))

/-- The algebraic identity behind the derivative of Mirzakhani's kernel `R`. -/
lemma Hker_add_Hker_div_two (x y z : ℝ) :
    (Hker z (x + y) + Hker z (x - y)) / 2 =
      1 - (Real.sinh ((x + z) / 2) * (1 / 2) / (Real.cosh (y / 2) + Real.cosh ((x + z) / 2)) -
        Real.sinh ((x - z) / 2) * (1 / 2) / (Real.cosh (y / 2) + Real.cosh ((x - z) / 2))) := by
  set u := Real.exp (x / 2) with hu
  set v := Real.exp (y / 2) with hv
  set w := Real.exp (z / 2) with hw
  have pu : 0 < u := Real.exp_pos _
  have pv : 0 < v := Real.exp_pos _
  have pw : 0 < w := Real.exp_pos _
  have hA : Real.exp ((x + z) / 2) = u * w := by rw [hu, hw, ← Real.exp_add]; ring_nf
  have hB : Real.exp (-((x + z) / 2)) = u⁻¹ * w⁻¹ := by rw [Real.exp_neg, hA]; field_simp
  have hC : Real.exp ((x - z) / 2) = u * w⁻¹ := by
    rw [hu, hw, ← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hD : Real.exp (-((x - z) / 2)) = u⁻¹ * w := by rw [Real.exp_neg, hC]; field_simp
  have hF : Real.exp (-(y / 2)) = v⁻¹ := by rw [Real.exp_neg, hv]
  have hG : Real.exp ((z + (x + y)) / 2) = w * (u * v) := by
    rw [hu, hv, hw, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hH : Real.exp ((z - (x + y)) / 2) = w * (u⁻¹ * v⁻¹) := by
    rw [hu, hv, hw, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hI : Real.exp ((z + (x - y)) / 2) = w * (u * v⁻¹) := by
    rw [hu, hv, hw, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hJ : Real.exp ((z - (x - y)) / 2) = w * (u⁻¹ * v) := by
    rw [hu, hv, hw, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; ring_nf
  simp only [Hker, Real.cosh_eq, Real.sinh_eq, hA, hB, hC, hD, hF, hG, hH, hI, hJ, ← hv]
  have q1 : 0 < 1 + w * (u * v) := by positivity
  have q2 : 0 < 1 + w * (u⁻¹ * v⁻¹) := by positivity
  have q3 : 0 < 1 + w * (u * v⁻¹) := by positivity
  have q4 : 0 < 1 + w * (u⁻¹ * v) := by positivity
  have q5 : 0 < (v + v⁻¹) / 2 + (u * w + u⁻¹ * w⁻¹) / 2 := by positivity
  have q6 : 0 < (v + v⁻¹) / 2 + (u * w⁻¹ + u⁻¹ * w) / 2 := by positivity
  field_simp
  ring

/-- **Mirzakhani's kernel identity**:
`∂R/∂x (x, y, z) = ½ (H(z, x + y) + H(z, x - y))`. -/
lemma hasDerivAt_Rker (x y z : ℝ) :
    HasDerivAt (fun t : ℝ => Rker t y z) ((Hker z (x + y) + Hker z (x - y)) / 2) x := by
  have hp1 : (0 : ℝ) < Real.cosh (y / 2) + Real.cosh ((x + z) / 2) := by
    have := Real.cosh_pos ((x + z) / 2); have := Real.cosh_pos (y / 2); linarith
  have hp2 : (0 : ℝ) < Real.cosh (y / 2) + Real.cosh ((x - z) / 2) := by
    have := Real.cosh_pos ((x - z) / 2); have := Real.cosh_pos (y / 2); linarith
  have hfun : (fun t : ℝ => Rker t y z) = fun t : ℝ => t -
      (Real.log (Real.cosh (y / 2) + Real.cosh ((t + z) / 2)) -
        Real.log (Real.cosh (y / 2) + Real.cosh ((t - z) / 2))) := by
    funext t
    have q1 : (0 : ℝ) < Real.cosh (y / 2) + Real.cosh ((t + z) / 2) := by
      have := Real.cosh_pos ((t + z) / 2); have := Real.cosh_pos (y / 2); linarith
    have q2 : (0 : ℝ) < Real.cosh (y / 2) + Real.cosh ((t - z) / 2) := by
      have := Real.cosh_pos ((t - z) / 2); have := Real.cosh_pos (y / 2); linarith
    rw [Rker, Real.log_div (ne_of_gt q1) (ne_of_gt q2)]
  rw [hfun]
  have d1 : HasDerivAt (fun t : ℝ => Real.cosh ((t + z) / 2)) (Real.sinh ((x + z) / 2) * (1 / 2)) x := by
    simpa using (((hasDerivAt_id x).add_const z).div_const 2).cosh
  have d2 : HasDerivAt (fun t : ℝ => Real.cosh ((t - z) / 2)) (Real.sinh ((x - z) / 2) * (1 / 2)) x := by
    simpa using (((hasDerivAt_id x).sub_const z).div_const 2).cosh
  have l1 := (d1.const_add (Real.cosh (y / 2))).log (ne_of_gt hp1)
  have l2 := (d2.const_add (Real.cosh (y / 2))).log (ne_of_gt hp2)
  have hd := (hasDerivAt_id x).sub (l1.sub l2)
  convert hd using 1
  rw [Hker_add_Hker_div_two]

/-! ## Squaring `2πi` -/

lemma two_pi_I_sq : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
  have : (Complex.I) ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [this]
  ring

/-! ## String equations -/

/-- The elementary integral `∫₀^L y dy = L²/2`, as a complex-valued statement. -/
lemma integral_id_ofReal (L : ℝ) : (∫ y in (0 : ℝ)..L, (y : ℂ) * V03) = ((L : ℂ) ^ 2) / 2 := by
  have hfun : (fun y : ℝ => (y : ℂ) * V03) = fun y : ℝ => ((y : ℝ) : ℂ) := by
    funext y; simp [V03]
  rw [hfun, intervalIntegral.integral_ofReal, integral_id]
  push_cast
  ring

/-- The integral `∫₀^L y V_{1,1}(y) dy = L⁴/192 + π²L²/24`. -/
lemma integral_V11 (L : ℝ) :
    (∫ y in (0 : ℝ)..L, (y : ℂ) * V11 (y : ℂ))
      = ((L : ℂ) ^ 4) / 192 + (Real.pi : ℂ) ^ 2 * ((L : ℂ) ^ 2) / 24 := by
  have hfun : (fun y : ℝ => (y : ℂ) * V11 (y : ℂ))
      = fun y : ℝ => ((y * (y ^ 2 + 4 * Real.pi ^ 2) / 48 : ℝ) : ℂ) := by
    funext y; simp only [V11]; push_cast; ring
  have hreal : (∫ y in (0 : ℝ)..L, y * (y ^ 2 + 4 * Real.pi ^ 2) / 48)
      = L ^ 4 / 192 + Real.pi ^ 2 * L ^ 2 / 24 := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) L,
        HasDerivAt (fun y : ℝ => y ^ 4 / 192 + Real.pi ^ 2 * y ^ 2 / 24)
          (t * (t ^ 2 + 4 * Real.pi ^ 2) / 48) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => y ^ 4 / 192 + Real.pi ^ 2 * y ^ 2 / 24)
          ((4 * t ^ 3) / 192 + Real.pi ^ 2 * (2 * t) / 24) t := by
        have a := (hasDerivAt_pow 4 t).div_const 192
        have b := ((hasDerivAt_pow 2 t).const_mul (Real.pi ^ 2)).div_const 24
        simpa using a.add b
      convert h1 using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    · norm_num
    · apply Continuous.intervalIntegrable; fun_prop
  rw [hfun, intervalIntegral.integral_ofReal, hreal]
  push_cast
  ring

/-- **String equation** for `V_{0,4}`: it reduces `V_{0,4}` to `V_{0,3}`. -/
lemma string_V04 (L₁ L₂ L₃ : ℝ) :
    V04 L₁ L₂ L₃ (2 * Real.pi * Complex.I) =
      (∫ y in (0 : ℝ)..L₁, (y : ℂ) * V03) + (∫ y in (0 : ℝ)..L₂, (y : ℂ) * V03) +
        (∫ y in (0 : ℝ)..L₃, (y : ℂ) * V03) := by
  rw [integral_id_ofReal, integral_id_ofReal, integral_id_ofReal, V04, two_pi_I_sq]
  ring

/-- **String equation** for `V_{1,2}`: it reduces `V_{1,2}` to `V_{1,1}`. -/
lemma string_V12 (L : ℝ) :
    V12 L (2 * Real.pi * Complex.I) = ∫ y in (0 : ℝ)..L, (y : ℂ) * V11 (y : ℂ) := by
  rw [integral_V11, V12, two_pi_I_sq]
  ring

/-! ## Dilaton (Do) equations -/

/-- **Dilaton equation** for `V_{0,4}`: `∂V_{0,4}/∂b₄ (b, 2πi) = 2πi (2g-2+n) V_{0,3}` with
`g = 0`, `n = 3`. -/
lemma dilaton_V04 (b₁ b₂ b₃ : ℂ) :
    deriv (fun b : ℂ => V04 b₁ b₂ b₃ b) (2 * Real.pi * Complex.I) =
      2 * Real.pi * Complex.I * V03 := by
  have h : HasDerivAt (fun b : ℂ => V04 b₁ b₂ b₃ b) (2 * Real.pi * Complex.I)
      (2 * Real.pi * Complex.I) := by
    simp only [V04]
    have h0 := (((hasDerivAt_pow 2 (2 * (Real.pi : ℂ) * Complex.I)).const_add
      (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2)).add_const (4 * (Real.pi : ℂ) ^ 2)).div_const 2
    convert h0 using 1
    push_cast
    ring
  rw [h.deriv, V03]
  ring

/-- **Dilaton equation** for `V_{1,2}`: `∂V_{1,2}/∂b₂ (b₁, 2πi) = 2πi (2g-2+n) V_{1,1}(b₁)` with
`g = 1`, `n = 1`. -/
lemma dilaton_V12 (b₁ : ℂ) :
    deriv (fun b : ℂ => V12 b₁ b) (2 * Real.pi * Complex.I) =
      2 * Real.pi * Complex.I * V11 b₁ := by
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  have h : HasDerivAt (fun b : ℂ => V12 b₁ b)
      ((2 * c * (12 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2 + c ^ 2) +
        (4 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2 + c ^ 2) * (2 * c)) / 192) c := by
    have h1 : HasDerivAt (fun b : ℂ => 4 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2 + b ^ 2) (2 * c) c := by
      simpa using ((hasDerivAt_pow 2 c).const_add (4 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2))
    have h2 : HasDerivAt (fun b : ℂ => 12 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2 + b ^ 2) (2 * c) c := by
      simpa using ((hasDerivAt_pow 2 c).const_add (12 * (Real.pi : ℂ) ^ 2 + b₁ ^ 2))
    simpa only [V12] using (h1.mul h2).div_const 192
  rw [h.deriv, V11, hc, two_pi_I_sq]
  ring

/-! ## The main statement -/

/-- **Mirzakhani's recursion for Weil–Petersson volumes** (base cases and
Lean-checked reductions).

The statement collects:

* the base cases of the recursion, `V_{0,3} = 1` and `V_{1,1}(b) = (b²+4π²)/48`,
  together with the next two volume polynomials `V_{0,4}` and `V_{1,2}`;
* the kernel identities `∂D/∂x(x,y,z) = H(y+z,x)` and
  `∂R/∂x(x,y,z) = ½(H(z,x+y) + H(z,x-y))` underlying the recursion;
* the **string equation** `V_{g,n+1}(L, 2πi) = Σ_k ∫₀^{L_k} y V_{g,n}(…, y, …) dy`
  verified for `(g,n) = (0,3)` and `(g,n) = (1,1)`;
* the **dilaton (Do) equation**
  `∂V_{g,n+1}/∂L_{n+1}(L, 2πi) = 2πi (2g - 2 + n) V_{g,n}(L)`
  verified for `(g,n) = (0,3)` and `(g,n) = (1,1)`.

The last two items are exactly the recursions obtained from Mirzakhani's
recursion by analytic continuation, and they determine `V_{0,4}` from `V_{0,3}`
and `V_{1,2}` from `V_{1,1}`. -/
theorem mirzakhani_WP_volume :
    -- base cases
    V03 = 1 ∧
    (∀ b : ℂ, V11 b = (b ^ 2 + 4 * (Real.pi : ℂ) ^ 2) / 48) ∧
    -- Mirzakhani's kernel identities
    (∀ x y z : ℝ, HasDerivAt (fun t : ℝ => Dker t y z) (Hker (y + z) x) x) ∧
    (∀ x y z : ℝ,
      HasDerivAt (fun t : ℝ => Rker t y z) ((Hker z (x + y) + Hker z (x - y)) / 2) x) ∧
    -- string equation, reducing V_{0,4} to V_{0,3}
    (∀ L₁ L₂ L₃ : ℝ,
      V04 L₁ L₂ L₃ (2 * Real.pi * Complex.I) =
        (∫ y in (0 : ℝ)..L₁, (y : ℂ) * V03) + (∫ y in (0 : ℝ)..L₂, (y : ℂ) * V03) +
          (∫ y in (0 : ℝ)..L₃, (y : ℂ) * V03)) ∧
    -- string equation, reducing V_{1,2} to V_{1,1}
    (∀ L : ℝ, V12 L (2 * Real.pi * Complex.I) = ∫ y in (0 : ℝ)..L, (y : ℂ) * V11 (y : ℂ)) ∧
    -- dilaton (Do) equation, reducing V_{0,4} to V_{0,3}
    (∀ b₁ b₂ b₃ : ℂ,
      deriv (fun b : ℂ => V04 b₁ b₂ b₃ b) (2 * Real.pi * Complex.I) =
        2 * Real.pi * Complex.I * V03) ∧
    -- dilaton (Do) equation, reducing V_{1,2} to V_{1,1}
    (∀ b₁ : ℂ,
      deriv (fun b : ℂ => V12 b₁ b) (2 * Real.pi * Complex.I) =
        2 * Real.pi * Complex.I * V11 b₁) :=
  ⟨rfl, fun _ => rfl, hasDerivAt_Dker, hasDerivAt_Rker, string_V04, string_V12, dilaton_V04,
    dilaton_V12⟩

end Frontier

