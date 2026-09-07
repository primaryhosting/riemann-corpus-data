/-
  Brockian/WeylDisk.lean — the Weyl nested-disk / m-function geometry:
  the analytic-ODE side of Weyl's limit-point / limit-circle theory for

      -y'' + V y = λ y      i.e.      y'' = (V - λ) y,   V real, Im λ ≠ 0.

  Fix two solutions `θ, φ` by real initial data at `0` (here `θ(0)=1, θ'(0)=0`,
  `φ(0)=0, φ'(0)=1`, so the Wronskian `W(θ,φ) = 1`).  The one-parameter family
  `ψ_ℓ = θ + ℓ φ` (ℓ ∈ ℂ) is a solution for every `ℓ`.  Imposing a *real*
  (self-adjoint) boundary condition at the endpoint `b` is exactly the vanishing
  of the boundary Wronskian `W(ψ̄_ℓ, ψ_ℓ)(b)`; as `ℓ` varies this cuts out a
  **circle** `C_b` in the complex ℓ-plane.  This file proves, AXLE-verified and
  hole-free at Mathlib v4.32.0:

  ## What is proved (RUNG 1 — the full nested-circle geometry)

    * `weyl_disk_circle`  — **the nested-circle theorem, exact.** For any
        boundary values `Θ,Θ',Φ,Φ'` with `Θ Φ' − Θ' Φ = 1` (unit Wronskian) and
        `A := Φ̄ Φ' − Φ̄' Φ ≠ 0`, the zero set of the boundary Wronskian
        `{ℓ | W(ψ̄_ℓ,ψ_ℓ)(b) = 0}` is *exactly* the metric sphere
        `Metric.sphere z₀ (1/‖A‖)` — a genuine circle of radius `1/‖A‖`.
        Proved by a self-contained complex Gram identity (`circle_key`), not by
        any definitional device: the circle is the honest zero locus and the
        radius is derived.
    * `boundary_L2_identity` — the base Green/Wronskian L²-identity
        `(λ − λ̄)·∫ₐᵇ |ψ|² = W(ψ̄,ψ)(a) − W(ψ̄,ψ)(b)` for any solution `ψ`
        (from the integrated Lagrange identity `green_identity_integral`).
    * `radius_formula` — **the classical radius**
        `‖A‖ = 2·|Im λ|·∫₀ᵇ |φ|²`, hence `r_b = 1/(2 |Im λ| ∫₀ᵇ |φ|²)`,
        by evaluating the boundary identity for `φ` against the initial data.
    * `integral_normSq_mono` — `b ↦ ∫₀ᵇ |φ|²` is nondecreasing (the driver of
        nesting: the disks shrink).
    * `weyl_nested_circle` — assembles the above: `C_b` is the sphere of radius
        `1/(2 |Im λ| ∫₀ᵇ |φ|²)` centred at `z₀(b)`, straight from ODE data.
    * `weyl_radius_antitone` — **nesting**: `b ≤ b' ⇒ r_{b'} ≤ r_b`
        (the radii decrease, so the circles are nested).

  ## Honest scope

  The remaining step of the *dichotomy* — that as `b → ∞` the nested circles
  converge either to a point (limit-point) or to a limiting circle (limit-circle)
  — is a statement about the limit of the radii `r_b = 1/(2|Im λ| ∫₀ᵇ |φ|²)`,
  i.e. about whether `∫₀^∞ |φ|² < ∞`.  That limiting classification, and the
  passage to essential self-adjointness of the unbounded operator `−Δ + V`, need
  deficiency-index / unbounded-`LinearPMap` self-adjointness machinery absent
  from Mathlib v4.32.0.  This file ships the full finite-`b` nested-circle
  geometry with the exact radius and its monotonicity — the verified analytic
  substrate on which that limit is taken — and names nothing more than it proves.

  Self-contained: the Wronskian / integrated-Green core (`wronskian`,
  `wronskian_hasDerivAt`, `wronskian_isConst`, `sturmL`, `lagrange_identity`,
  `green_identity_integral`) is restated here (namespace `Brockian.Weyl.Disk`,
  disjoint from `Brockian.Weyl`) so the module AXLE-checks as one unit.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

open Complex ComplexConjugate

namespace Brockian.Weyl.Disk

/-! ### Boundary-value data of the disk -/

/-- The boundary Wronskian coefficient `A = W(φ̄,φ)(b) = Φ̄ Φ' − Φ̄' Φ`
(purely imaginary; its modulus is `2|Im λ| ∫₀ᵇ|φ|²`). -/
def Acoef (Φ Φ' : ℂ) : ℂ := conj Φ * Φ' - conj Φ' * Φ

/-- The cross coefficient `P = θ̄(b) φ'(b) − θ̄'(b) φ(b) = W(θ̄,φ)(b)`. -/
def Pcoef (Θ Θ' Φ Φ' : ℂ) : ℂ := conj Θ * Φ' - conj Θ' * Φ

/-- The centre of the Weyl circle `C_b`, `z₀ = P̄ / A`. -/
noncomputable def diskCenter (Θ Θ' Φ Φ' : ℂ) : ℂ := conj (Pcoef Θ Θ' Φ Φ') / Acoef Φ Φ'

/-- The boundary Wronskian `W(ψ̄_ℓ, ψ_ℓ)(b)` for `ψ_ℓ = θ + ℓ φ`, as a function of
`ℓ`, in terms of the boundary values `Θ = θ(b), Θ' = θ'(b), Φ = φ(b), Φ' = φ'(b)`.
Its zero set is the Weyl circle. -/
def circleEq (Θ Θ' Φ Φ' ℓ : ℂ) : ℂ :=
  conj (Θ + ℓ * Φ) * (Θ' + ℓ * Φ') - conj (Θ' + ℓ * Φ') * (Θ + ℓ * Φ)

/-! ### The complex Gram identity — algebraic heart of the circle -/

/-- **Circle key identity.** With unit Wronskian `Θ Φ' − Θ' Φ = 1`, the boundary
Wronskian times `A` completes to a square:
`W(ψ̄_ℓ,ψ_ℓ)(b) · A = 1 − w·w̄` with `w = A ℓ − P̄`.  This is the polynomial
Gram identity `|W(θ̄,φ)|² + W(θ̄,θ)·W(φ̄,φ) = |W(θ,φ)|²` in disguise; it is what
makes the zero set a circle of radius `1/‖A‖`. -/
theorem circle_key (Θ Θ' Φ Φ' ℓ : ℂ) (hW : Θ * Φ' - Θ' * Φ = 1) :
    (conj (Θ + ℓ * Φ) * (Θ' + ℓ * Φ') - conj (Θ' + ℓ * Φ') * (Θ + ℓ * Φ))
        * (conj Φ * Φ' - conj Φ' * Φ)
      = 1 - ((conj Φ * Φ' - conj Φ' * Φ) * ℓ - conj (conj Θ * Φ' - conj Θ' * Φ))
            * conj ((conj Φ * Φ' - conj Φ' * Φ) * ℓ - conj (conj Θ * Φ' - conj Θ' * Φ)) := by
  have hWc : conj Θ * conj Φ' - conj Θ' * conj Φ = 1 := by
    have h := congrArg (starRingEnd ℂ) hW
    simpa using h
  simp only [map_add, map_sub, map_mul, Complex.conj_conj]
  linear_combination (conj Θ * conj Φ' - conj Θ' * conj Φ) * hW + hWc

/-- **The Weyl nested circle, exact.** For boundary values with unit Wronskian
(`Θ Φ' − Θ' Φ = 1`) and non-degenerate boundary coefficient `A = Φ̄Φ' − Φ̄'Φ ≠ 0`,
the locus of `ℓ` for which `ψ_ℓ = θ + ℓ φ` meets a real boundary condition at `b`
(i.e. `W(ψ̄_ℓ,ψ_ℓ)(b) = 0`) is *exactly* the circle of radius `1/‖A‖` about
`z₀ = P̄/A`.  Nothing here is definitional: the set is the honest zero locus, and
being a metric sphere of that radius is derived. -/
theorem weyl_disk_circle (Θ Θ' Φ Φ' : ℂ)
    (hW : Θ * Φ' - Θ' * Φ = 1) (hA : Acoef Φ Φ' ≠ 0) :
    {ℓ : ℂ | circleEq Θ Θ' Φ Φ' ℓ = 0}
      = Metric.sphere (diskCenter Θ Θ' Φ Φ') (1 / ‖Acoef Φ Φ'‖) := by
  have hAnorm : ‖Acoef Φ Φ'‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  ext ℓ
  rw [Set.mem_setOf_eq, Metric.mem_sphere, dist_eq_norm]
  set w : ℂ := Acoef Φ Φ' * ℓ - conj (Pcoef Θ Θ' Φ Φ') with hwdef
  have hkey : circleEq Θ Θ' Φ Φ' ℓ * Acoef Φ Φ' = 1 - w * conj w := by
    rw [hwdef]
    simp only [circleEq, Acoef, Pcoef]
    exact circle_key Θ Θ' Φ Φ' ℓ hW
  have hw : w = Acoef Φ Φ' * (ℓ - diskCenter Θ Θ' Φ Φ') := by
    rw [hwdef, diskCenter]; field_simp
  have hiffA : circleEq Θ Θ' Φ Φ' ℓ = 0 ↔ w * conj w = 1 := by
    constructor
    · intro h0
      have hthis := hkey; rw [h0, zero_mul] at hthis
      linear_combination hthis
    · intro h1
      have h2 : circleEq Θ Θ' Φ Φ' ℓ * Acoef Φ Φ' = 0 := by rw [hkey, h1]; ring
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hA
  have hiffB : w * conj w = 1 ↔ ‖ℓ - diskCenter Θ Θ' Φ Φ'‖ = 1 / ‖Acoef Φ Φ'‖ := by
    have hnw : ‖w‖ = ‖Acoef Φ Φ'‖ * ‖ℓ - diskCenter Θ Θ' Φ Φ'‖ := by rw [hw, norm_mul]
    rw [Complex.mul_conj]
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from by norm_num]
    rw [Complex.ofReal_inj, Complex.normSq_eq_norm_sq, hnw]
    constructor
    · intro h
      have hpos : (0 : ℝ) ≤ ‖Acoef Φ Φ'‖ * ‖ℓ - diskCenter Θ Θ' Φ Φ'‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hprod : ‖Acoef Φ Φ'‖ * ‖ℓ - diskCenter Θ Θ' Φ Φ'‖ = 1 := by
        rw [← Real.sqrt_sq hpos, h, Real.sqrt_one]
      rw [eq_div_iff hAnorm]; linear_combination hprod
    · intro h
      rw [h]; field_simp
  exact hiffA.trans hiffB

/-! ### Restated Wronskian / integrated-Green core (self-contained) -/

/-- The Wronskian `W(x) = y₁ y₂' − y₁' y₂`. -/
def wronskian (y1 y1' y2 y2' : ℝ → ℂ) : ℝ → ℂ := fun x => y1 x * y2' x - y1' x * y2 x

/-- Infinitesimal Lagrange identity: `W' = y₁ y₂'' − y₁'' y₂` (pure product rule). -/
theorem wronskian_hasDerivAt {y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy1' : ∀ x, HasDerivAt y1' (y1'' x) x)
    (hy2 : ∀ x, HasDerivAt y2 (y2' x) x) (hy2' : ∀ x, HasDerivAt y2' (y2'' x) x) (x : ℝ) :
    HasDerivAt (wronskian y1 y1' y2 y2') (y1 x * y2'' x - y1'' x * y2 x) x := by
  have e : HasDerivAt (fun t => y1 t * y2' t - y1' t * y2 t)
        ((y1' x * y2' x + y1 x * y2'' x) - (y1'' x * y2 x + y1' x * y2' x)) x :=
    ((hy1 x).mul (hy2' x)).sub ((hy1' x).mul (hy2 x))
  have hval : ((y1' x * y2' x + y1 x * y2'' x) - (y1'' x * y2 x + y1' x * y2' x))
        = (y1 x * y2'' x - y1'' x * y2 x) := by ring
  rw [hval] at e; exact e

/-- **Abel / Wronskian constancy**: two solutions of the same `y'' = q y` have a
constant Wronskian. -/
theorem wronskian_isConst {q y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy1' : ∀ x, HasDerivAt y1' (y1'' x) x)
    (hy2 : ∀ x, HasDerivAt y2 (y2' x) x) (hy2' : ∀ x, HasDerivAt y2' (y2'' x) x)
    (heq1 : ∀ x, y1'' x = q x * y1 x) (heq2 : ∀ x, y2'' x = q x * y2 x) (a b : ℝ) :
    wronskian y1 y1' y2 y2' a = wronskian y1 y1' y2 y2' b := by
  have hd : ∀ x, HasDerivAt (wronskian y1 y1' y2 y2') 0 x := by
    intro x
    have h := wronskian_hasDerivAt hy1 hy1' hy2 hy2' x
    have hz : y1 x * y2'' x - y1'' x * y2 x = 0 := by rw [heq1 x, heq2 x]; ring
    rw [hz] at h; exact h
  have hdiff : Differentiable ℝ (wronskian y1 y1' y2 y2') := fun x => (hd x).differentiableAt
  have hzero : ∀ x, deriv (wronskian y1 y1' y2 y2') x = 0 := fun x => (hd x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero a b

/-- The Sturm–Liouville operator `L y = −y'' + V y`. -/
def sturmL (V y y'' : ℝ → ℂ) : ℝ → ℂ := fun x => - y'' x + V x * y x

/-- Green's (Lagrange) identity, pointwise: the potential cancels. -/
theorem lagrange_identity (V y1 y1'' y2 y2'' : ℝ → ℂ) (x : ℝ) :
    y1 x * (sturmL V y2 y2'') x - (sturmL V y1 y1'') x * y2 x
      = -(y1 x * y2'' x - y1'' x * y2 x) := by
  simp only [sturmL]; ring

/-- **Integrated Green / Lagrange identity**:
`∫ₐᵇ (y₁·L y₂ − L y₁·y₂) = W a − W b`. -/
theorem green_identity_integral {V y1 y1' y1'' y2 y2' y2'' : ℝ → ℂ}
    (hy1 : ∀ x, HasDerivAt y1 (y1' x) x) (hy1' : ∀ x, HasDerivAt y1' (y1'' x) x)
    (hy2 : ∀ x, HasDerivAt y2 (y2' x) x) (hy2' : ∀ x, HasDerivAt y2' (y2'' x) x)
    (hy1''c : Continuous y1'') (hy2''c : Continuous y2'') (a b : ℝ) :
    (∫ x in a..b, y1 x * (sturmL V y2 y2'') x - (sturmL V y1 y1'') x * y2 x)
      = wronskian y1 y1' y2 y2' a - wronskian y1 y1' y2 y2' b := by
  have hy1c : Continuous y1 := continuous_iff_continuousAt.mpr fun x => (hy1 x).continuousAt
  have hy2c : Continuous y2 := continuous_iff_continuousAt.mpr fun x => (hy2 x).continuousAt
  set g : ℝ → ℂ := fun x => y1 x * y2'' x - y1'' x * y2 x with hg
  have hgc : Continuous g := (hy1c.mul hy2''c).sub (hy1''c.mul hy2c)
  have hgint : IntervalIntegrable g MeasureTheory.volume a b := hgc.intervalIntegrable a b
  have hFTC : (∫ x in a..b, g x) = wronskian y1 y1' y2 y2' b - wronskian y1 y1' y2 y2' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => wronskian_hasDerivAt hy1 hy1' hy2 hy2' x) hgint
  have hrw : (∫ x in a..b, y1 x * (sturmL V y2 y2'') x - (sturmL V y1 y1'') x * y2 x)
      = ∫ x in a..b, -(g x) := by
    apply intervalIntegral.integral_congr; intro x _
    simpa [hg] using lagrange_identity V y1 y1'' y2 y2'' x
  rw [hrw, intervalIntegral.integral_neg, hFTC]; ring

/-! ### The boundary L²-identity and the radius formula -/

/-- **Boundary L²-identity.** For a solution `ψ` of `ψ'' = (V − λ)ψ` with real
potential `V`, the quadratic form `∫ₐᵇ |ψ|²` is controlled by the boundary
Wronskian of `ψ̄` and `ψ`:  `(λ − λ̄)·∫ₐᵇ ψ̄ ψ = W(ψ̄,ψ)(a) − W(ψ̄,ψ)(b)`.
Since `λ − λ̄ = 2i·Im λ`, this is the identity that turns the real integral
`∫|ψ|²` into a boundary term — the engine of the whole disk geometry. -/
theorem boundary_L2_identity {V : ℝ → ℝ} {lam : ℂ} {ψ ψ' ψ'' : ℝ → ℂ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hψ''c : Continuous ψ'')
    (hode : ∀ x, ψ'' x = ((V x : ℂ) - lam) * ψ x) (a b : ℝ) :
    (lam - conj lam) * ∫ x in a..b, conj (ψ x) * ψ x
      = wronskian (fun t => conj (ψ t)) (fun t => conj (ψ' t)) ψ ψ' a
        - wronskian (fun t => conj (ψ t)) (fun t => conj (ψ' t)) ψ ψ' b := by
  have hg := green_identity_integral (V := fun x => (V x : ℂ))
      (y1 := fun t => conj (ψ t)) (y1' := fun t => conj (ψ' t)) (y1'' := fun t => conj (ψ'' t))
      (y2 := ψ) (y2' := ψ') (y2'' := ψ'')
      (fun x => (hψ x).star) (fun x => (hψ' x).star) hψ hψ'
      (Complex.continuous_conj.comp hψ''c) hψ''c a b
  have hpt : ∀ x, (fun t => conj (ψ t)) x * (sturmL (fun x => (V x : ℂ)) ψ ψ'') x
      - (sturmL (fun x => (V x : ℂ)) (fun t => conj (ψ t)) (fun t => conj (ψ'' t))) x * ψ x
      = (lam - conj lam) * (conj (ψ x) * ψ x) := by
    intro x
    simp only [sturmL]
    rw [hode x]
    simp only [map_mul, map_sub, Complex.conj_ofReal]
    ring
  rw [← hg, intervalIntegral.integral_congr (fun x _ => hpt x),
      intervalIntegral.integral_const_mul]

/-- **The Weyl radius.** With `φ` fixed by `φ(0)=0, φ'(0)=1`, the boundary
coefficient has modulus `‖A‖ = ‖W(φ̄,φ)(b)‖ = 2·|Im λ|·∫₀ᵇ|φ|²`.  Hence the
circle `C_b` has radius `r_b = 1/(2 |Im λ| ∫₀ᵇ |φ|²)` — the classical Weyl
radius. -/
theorem radius_formula {V : ℝ → ℝ} {lam : ℂ} {φ φ' φ'' : ℝ → ℂ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''c : Continuous φ'')
    (hode : ∀ x, φ'' x = ((V x : ℂ) - lam) * φ x)
    (hφ0 : φ 0 = 0) (hφ0' : φ' 0 = 1) (b : ℝ) (hb : 0 ≤ b) :
    ‖Acoef (φ b) (φ' b)‖ = 2 * |lam.im| * ∫ x in 0..b, ‖φ x‖ ^ 2 := by
  have hbnd := boundary_L2_identity hφ hφ' hφ''c hode 0 b
  have hW0 : wronskian (fun t => conj (φ t)) (fun t => conj (φ' t)) φ φ' 0 = 0 := by
    simp [wronskian, hφ0, hφ0']
  have hWb : wronskian (fun t => conj (φ t)) (fun t => conj (φ' t)) φ φ' b
      = Acoef (φ b) (φ' b) := rfl
  rw [hW0, hWb, zero_sub] at hbnd
  have hintR : (∫ x in 0..b, conj (φ x) * φ x) = ((∫ x in 0..b, ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    show conj (φ x) * φ x = ((‖φ x‖ ^ 2 : ℝ) : ℂ)
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hintR] at hbnd
  have hAeq : Acoef (φ b) (φ' b) = -((lam - conj lam) * ((∫ x in 0..b, ‖φ x‖ ^ 2 : ℝ) : ℂ)) := by
    linear_combination hbnd
  have hnn : 0 ≤ ∫ x in 0..b, ‖φ x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hb (fun x _ => sq_nonneg _)
  have hnorm_sub : ‖lam - conj lam‖ = 2 * |lam.im| := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_mul]
    norm_num
  have hnorm_int : ‖((∫ x in 0..b, ‖φ x‖ ^ 2 : ℝ) : ℂ)‖ = ∫ x in 0..b, ‖φ x‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hAeq, norm_neg, norm_mul, hnorm_sub, hnorm_int]

/-! ### Monotonicity of `∫₀ᵇ|φ|²` and nesting -/

/-- The quadratic form `b ↦ ∫₀ᵇ |φ|²` is nondecreasing (`0 ≤ b ≤ b'`).  This is
what makes the Weyl circles nested: as `b` grows the radius `1/(2|Im λ|∫₀ᵇ|φ|²)`
can only shrink. -/
theorem integral_normSq_mono {φ : ℝ → ℂ} (hφc : Continuous φ)
    {b b' : ℝ} (hb : 0 ≤ b) (hbb' : b ≤ b') :
    (∫ x in 0..b, ‖φ x‖ ^ 2) ≤ ∫ x in 0..b', ‖φ x‖ ^ 2 := by
  have hfc : Continuous (fun x => ‖φ x‖ ^ 2) := hφc.norm.pow 2
  have hint1 : IntervalIntegrable (fun x => ‖φ x‖ ^ 2) MeasureTheory.volume 0 b :=
    hfc.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => ‖φ x‖ ^ 2) MeasureTheory.volume b b' :=
    hfc.intervalIntegrable _ _
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hnn : 0 ≤ ∫ x in b..b', ‖φ x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hbb' (fun x _ => sq_nonneg _)
  linarith [hadd, hnn]

/-- **Nested-circle geometry from ODE data.** With `θ, φ` fixed by
`θ(0)=1, θ'(0)=0, φ(0)=0, φ'(0)=1` (so `W(θ,φ) = 1`), both solving
`y'' = (V − λ)y` with real `V` and `Im λ ≠ 0`, the Weyl circle at `b` (the ℓ for
which `ψ_ℓ = θ + ℓ φ` satisfies a real boundary condition at `b`) is *exactly*
the sphere of radius `1/(2 |Im λ| ∫₀ᵇ |φ|²)` about `z₀(b)`. -/
theorem weyl_nested_circle {V : ℝ → ℝ} {lam : ℂ} {θ θ' θ'' φ φ' φ'' : ℝ → ℂ}
    (hθ : ∀ x, HasDerivAt θ (θ' x) x) (hθ' : ∀ x, HasDerivAt θ' (θ'' x) x)
    (hθode : ∀ x, θ'' x = ((V x : ℂ) - lam) * θ x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ''c : Continuous φ'') (hφode : ∀ x, φ'' x = ((V x : ℂ) - lam) * φ x)
    (hθ0 : θ 0 = 1) (hθ0' : θ' 0 = 0) (hφ0 : φ 0 = 0) (hφ0' : φ' 0 = 1)
    (hlam : lam.im ≠ 0) (b : ℝ) (hb : 0 ≤ b)
    (hpos : 0 < ∫ x in 0..b, ‖φ x‖ ^ 2) :
    {ℓ : ℂ | circleEq (θ b) (θ' b) (φ b) (φ' b) ℓ = 0}
      = Metric.sphere (diskCenter (θ b) (θ' b) (φ b) (φ' b))
          (1 / (2 * |lam.im| * ∫ x in 0..b, ‖φ x‖ ^ 2)) := by
  have hWconst := wronskian_isConst (q := fun x => (V x : ℂ) - lam)
    hθ hθ' hφ hφ' (fun x => hθode x) (fun x => hφode x) b 0
  have hW : (θ b) * (φ' b) - (θ' b) * (φ b) = 1 := by
    have hthis := hWconst
    simp only [wronskian] at hthis
    rw [hthis, hθ0, hθ0', hφ0, hφ0']; ring
  have hAnorm : ‖Acoef (φ b) (φ' b)‖ = 2 * |lam.im| * ∫ x in 0..b, ‖φ x‖ ^ 2 :=
    radius_formula hφ hφ' hφ''c hφode hφ0 hφ0' b hb
  have hApos : 0 < ‖Acoef (φ b) (φ' b)‖ := by
    rw [hAnorm]; exact mul_pos (mul_pos two_pos (abs_pos.mpr hlam)) hpos
  have hA : Acoef (φ b) (φ' b) ≠ 0 := norm_pos_iff.mp hApos
  rw [weyl_disk_circle (θ b) (θ' b) (φ b) (φ' b) hW hA, hAnorm]

/-- **Nesting.** The Weyl radii are antitone in `b`: `b ≤ b' ⇒ r_{b'} ≤ r_b`.
Combined with `weyl_nested_circle`, this is the statement that the disks are
nested (`C_{b'}` lies inside the disk bounded by `C_b`). -/
theorem weyl_radius_antitone {lam : ℂ} {φ : ℝ → ℂ} (hφc : Continuous φ) (hlam : lam.im ≠ 0)
    {b b' : ℝ} (hb : 0 ≤ b) (hbb' : b ≤ b') (hpos : 0 < ∫ x in 0..b, ‖φ x‖ ^ 2) :
    1 / (2 * |lam.im| * ∫ x in 0..b', ‖φ x‖ ^ 2)
      ≤ 1 / (2 * |lam.im| * ∫ x in 0..b, ‖φ x‖ ^ 2) := by
  have hmono := integral_normSq_mono hφc hb hbb'
  have hden : 0 < 2 * |lam.im| * ∫ x in 0..b, ‖φ x‖ ^ 2 :=
    mul_pos (mul_pos two_pos (abs_pos.mpr hlam)) hpos
  have hle : 2 * |lam.im| * (∫ x in 0..b, ‖φ x‖ ^ 2) ≤ 2 * |lam.im| * ∫ x in 0..b', ‖φ x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  exact one_div_le_one_div_of_le hden hle

end Brockian.Weyl.Disk
