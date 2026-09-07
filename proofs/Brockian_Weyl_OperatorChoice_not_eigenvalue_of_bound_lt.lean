/-
  Brockian/WeylOperatorChoice.lean — operator-shape obstruction for the RH route.

  ## What is proved

  Gate 1 (ESA of −Δ+V) is necessary for a Hilbert–Pólya programme but **not
  sufficient** for RH. Bounded operators have eigenvalues controlled by any
  operator bound:

      ‖A v‖ ≤ C ‖v‖,  A v = μ • v,  v ≠ 0  ⇒  ‖μ‖ ≤ C.

  The Hilbert–Pólya correspondence realises a nontrivial ζ-zero `s` as the
  eigenvalue `t = −i(s − 1/2)` with modulus `‖s − 1/2‖`. Hence **no operator
  obeying a bound of size C** can realise a zero outside the closed ball of
  radius `C` about `1/2`.

  Instantiated on the prime-Gaussian multiplication operator (`C = 2`), the
  decaying potential is a Gate-1 test object, **not** a Hilbert–Pólya candidate.

  ## Honest non-claims

  * Does **not** prove RH, nor that no `BrockianSystem` exists.
  * Does **not** compute the essential spectrum of −Δ+V.
  * Does **not** assert infinitude of large zeros; the obstruction is
    *conditional on a zero outside the ball*.

  Owner: Grok (queue #3). Do not clobber without coordination.
  Verification (spec §2A): AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.SpectralGate1
import Brockian.RiemannScaffold

open MeasureTheory Complex
open Brockian.SpectralGate1 Brockian.RiemannScaffold

namespace Brockian.Weyl.OperatorChoice

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Eigenvalue bounds for bounded operators -/

/-- **Eigenvalues controlled by an operator bound.** If `‖A x‖ ≤ C ‖x‖` for all
`x` and `A v = μ • v` with `v ≠ 0`, then `‖μ‖ ≤ C`. -/
theorem norm_eigenvalue_le_of_bound (A : H →L[ℂ] H) {C : ℝ}
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖) {μ : ℂ} {v : H}
    (hv : v ≠ 0) (heig : A v = μ • v) : ‖μ‖ ≤ C := by
  have hle : ‖A v‖ ≤ C * ‖v‖ := hbd v
  rw [heig, norm_smul] at hle
  -- ‖μ‖ * ‖v‖ ≤ C * ‖v‖ and ‖v‖ > 0
  exact (le_of_mul_le_mul_right hle (norm_pos_iff.mpr hv))

/-- Special case via the operator norm. -/
theorem norm_eigenvalue_le_opNorm (A : H →L[ℂ] H) {μ : ℂ} {v : H}
    (hv : v ≠ 0) (heig : A v = μ • v) : ‖μ‖ ≤ ‖A‖ :=
  norm_eigenvalue_le_of_bound A (fun x => A.le_opNorm x) hv heig

/-- Outside a bound ball there is no eigenvector. -/
theorem not_eigenvalue_of_bound_lt (A : H →L[ℂ] H) {C : ℝ} {μ : ℂ}
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖) (hμ : C < ‖μ‖) (v : H) (hv : v ≠ 0) :
    A v ≠ μ • v := by
  intro heig
  exact (lt_irrefl _ ((norm_eigenvalue_le_of_bound A hbd hv heig).trans_lt hμ))

/-! ### BrockianSystem correspondence modulus -/

/-- The Hilbert–Pólya eigenvalue attached to a zero `s` has modulus `‖s − 1/2‖`. -/
theorem brockian_eigenvalue_norm (s : ℂ) :
    ‖(-I * (s - 1 / 2) : ℂ)‖ = ‖s - 1 / 2‖ := by
  rw [norm_mul, norm_neg, norm_I, one_mul]

/-- **Bounded-operator obstruction (abstract).** If `A` obeys bound `C` and `s` is
a nontrivial ζ-zero with `C < ‖s − 1/2‖`, then `A` cannot realise `s` as a
`BrockianSystem` eigenvalue. -/
theorem not_realize_zero_of_bound_lt (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (_hz : riemannZeta s = 0)
    (_htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (_hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖)
    (v : H) (hv : v ≠ 0) :
    A v ≠ (-I * (s - 1 / 2)) • v := by
  have hμ : C < ‖(-I * (s - 1 / 2) : ℂ)‖ := by rwa [brockian_eigenvalue_norm]
  exact not_eigenvalue_of_bound_lt A hbd hμ v hv

/-- Same obstruction for the full-domain `LinearPMap` view. -/
theorem not_realize_zero_of_toPMap (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖)
    (v : (A.toPMap ⊤).domain) (hv : (v : H) ≠ 0) :
    (A.toPMap ⊤) v ≠ (-I * (s - 1 / 2)) • (v : H) := by
  simpa [LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe] using
    not_realize_zero_of_bound_lt A hz htriv hs1 hbd hball (v : H) hv

/-! ### Candidate shapes (definitions, not claims) -/

/-- **Decaying potential candidate** — bounded continuous real potential.
Gate-1 test object; spectrally wrong shape for Hilbert–Pólya. -/
structure DecayingPotentialCandidate where
  V : ℝ → ℝ
  continuous : Continuous V
  M : ℝ
  bound : ∀ x, |V x| ≤ M
  M_nonneg : 0 ≤ M

/-- **Confining potential candidate** — growth `V(x) → +∞` as `|x| → ∞`.
No ESA or spectral claim is made; shape required for discrete spectrum. -/
structure ConfiningPotentialCandidate where
  V : ℝ → ℝ
  continuous : Continuous V
  confining : ∀ C : ℝ, ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → C ≤ V x

/-- The prime-Gaussian potential is a decaying candidate (bound `2`). -/
noncomputable def primeGaussian_decaying : DecayingPotentialCandidate where
  V := primeGaussian
  continuous := continuous_primeGaussian
  M := 2
  bound := abs_primeGaussian_le_two
  M_nonneg := by norm_num

/-! ### Instantiation on the prime-Gaussian multiplication operator -/

/-- Pointwise operator bound `‖M_V f‖ ≤ 2 ‖f‖` from the `mulLpCLM` construction. -/
theorem norm_primeGaussianMulCLM_le (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖primeGaussianMulCLM f‖ ≤ 2 * ‖f‖ := by
  -- `primeGaussianMulCLM` is definitionally `mulLpCLM … = mkContinuous (mulLpₗ …) 2 h`
  have hEq : primeGaussianMulCLM f =
      mulLpFun primeGaussianℂ primeGaussianℂ_memLp_top f := by
    simp only [primeGaussianMulCLM, mulLpCLM, LinearMap.mkContinuous_apply, mulLpₗ_apply]
  rw [hEq, Lp.norm_def, Lp.norm_def]
  have hfin : eLpNorm (f : ℝ → ℂ) 2 volume ≠ ⊤ := (Lp.memLp f).eLpNorm_ne_top
  have hbnd := eLpNorm_mulLpFun_le primeGaussianℂ primeGaussianℂ_memLp_top
    (by norm_num : (0 : ℝ) ≤ 2) (ae_of_all _ primeGaussianℂ_norm_le) f
  have htop : ENNReal.ofReal (2 : ℝ) * eLpNorm (f : ℝ → ℂ) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc (eLpNorm (mulLpFun primeGaussianℂ primeGaussianℂ_memLp_top f : ℝ → ℂ)
          2 volume).toReal
      ≤ (ENNReal.ofReal 2 * eLpNorm (f : ℝ → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono htop hbnd
    _ = 2 * (eLpNorm (f : ℝ → ℂ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]

/-- Operator-norm form of the same bound. -/
theorem primeGaussianMulCLM_opNorm_le_two : ‖primeGaussianMulCLM‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) norm_primeGaussianMulCLM_le

/-- **Prime-Gaussian obstruction.** If `s` is a nontrivial ζ-zero with
`2 < ‖s − 1/2‖`, then the prime-Gaussian multiplication operator cannot realise
`s` as a Hilbert–Pólya eigenvalue. -/
theorem primeGaussian_not_realize_large_zero {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hball : (2 : ℝ) < ‖s - 1 / 2‖)
    (v : Lp ℂ 2 (volume : Measure ℝ)) (hv : v ≠ 0) :
    primeGaussianMulCLM v ≠ (-I * (s - 1 / 2)) • v :=
  not_realize_zero_of_bound_lt primeGaussianMulCLM hz htriv hs1
    norm_primeGaussianMulCLM_le hball v hv

/-- Documentary packaging: RH needs an operator that can realise eigenvalues
outside every ball (unbounded / confining); a bound-`C` operator cannot. -/
theorem rh_operator_needs_unbounded_spectrum
    (A : H →L[ℂ] H) {C : ℝ} {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hbd : ∀ x, ‖A x‖ ≤ C * ‖x‖)
    (hball : C < ‖s - 1 / 2‖) :
    ¬ ∃ (v : H), v ≠ 0 ∧ A v = (-I * (s - 1 / 2)) • v := by
  rintro ⟨v, hv, heig⟩
  exact not_realize_zero_of_bound_lt A hz htriv hs1 hbd hball v hv heig

end Brockian.Weyl.OperatorChoice
