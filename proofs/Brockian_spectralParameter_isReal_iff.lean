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

import Mathlib

/-!
# A Hilbert–Pólya ("Brockian system") scaffold for the Riemann Hypothesis

This file sets up a spectral scaffold for the Riemann Hypothesis and proves the
*reduction* step rigorously:

* `Brockian.BrockianSystem μ` is a spectral realization of the complex number `μ`:
  an inner product space over `ℂ` together with a symmetric (self-adjoint)
  linear operator having `μ` as an eigenvalue.
* `Brockian.spectralParameter s = -I * (s - 1/2)` is the Hilbert–Pólya spectral
  parameter attached to a zero `s` of `ζ`; it is real exactly when `s.re = 1/2`.
* `Brockian.RiemannScaffold.BrockianRealization` is the named hypothesis: every
  nontrivial zero of `ζ` admits a Brockian system for its spectral parameter.
* `Brockian.RiemannScaffold.RH_of_BrockianSystem` derives `RiemannHypothesis`
  from that hypothesis. This is proved unconditionally, with no unproved steps.

To document that the scaffold is *faithful* (neither vacuous nor stronger than
needed) we also prove the converse,
`Brockian.RiemannScaffold.brockianRealization_of_RiemannHypothesis`, so that
`BrockianRealization ↔ RiemannHypothesis`
(`Brockian.RiemannScaffold.brockianRealization_iff_riemannHypothesis`).

Consequently the named hypothesis `BrockianRealization` is *exactly* the Riemann
Hypothesis; discharging it is the open problem itself, and it is not discharged
here. Every declaration in this file is fully proved.
-/

open Complex

namespace Brockian

/-- `s` is a nontrivial zero of the Riemann zeta function: a zero which is neither
one of the trivial zeros `-2*(n+1)` nor the pole `1`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- The Hilbert–Pólya spectral parameter attached to `s`, normalized so that it is
real precisely when `s` lies on the critical line. -/
noncomputable def spectralParameter (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

@[simp] lemma spectralParameter_im (s : ℂ) :
    (spectralParameter s).im = -(s.re - 1 / 2) := by
  simp [spectralParameter]

@[simp] lemma spectralParameter_re (s : ℂ) : (spectralParameter s).re = s.im := by
  simp [spectralParameter]

/-- The spectral parameter of `s` is real iff `s` lies on the critical line. -/
lemma spectralParameter_isReal_iff (s : ℂ) :
    (spectralParameter s).im = 0 ↔ s.re = 1 / 2 := by
  rw [spectralParameter_im]
  constructor <;> intro h <;> linarith

/-- A **Brockian system** for a complex number `μ`: a complex inner product space
equipped with a symmetric linear operator admitting `μ` as an eigenvalue.

This is the local (one zero at a time) form of the Hilbert–Pólya heuristic. -/
structure BrockianSystem (μ : ℂ) where
  /-- The underlying vector space of the system. -/
  carrier : Type
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace ℂ carrier]
  /-- The operator of the system. -/
  op : carrier →ₗ[ℂ] carrier
  /-- The operator is symmetric (formally self-adjoint). -/
  op_isSymmetric : op.IsSymmetric
  /-- `μ` occurs in the point spectrum of the operator. -/
  hasEigenvalue : Module.End.HasEigenvalue op μ

attribute [instance] BrockianSystem.normedAddCommGroup BrockianSystem.innerProductSpace

/-- Every complex number realized by a Brockian system is real. -/
theorem BrockianSystem.im_eq_zero {μ : ℂ} (B : BrockianSystem μ) : μ.im = 0 := by
  have h : (starRingEnd ℂ) μ = μ :=
    B.op_isSymmetric.conj_eigenvalue_eq_self B.hasEigenvalue
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- Conversely, every real number is realized by a Brockian system (a scalar
operator on the one-dimensional space `ℂ`). -/
noncomputable def BrockianSystem.ofReal (μ : ℂ) (hμ : μ.im = 0) : BrockianSystem μ where
  carrier := ℂ
  op := μ • LinearMap.id
  op_isSymmetric := by
    intro x y
    have hconj : (starRingEnd ℂ) μ = μ := Complex.conj_eq_iff_im.mpr hμ
    simp only [LinearMap.smul_apply, LinearMap.id_apply, RCLike.inner_apply,
      smul_eq_mul, map_mul, hconj]
    ring
  hasEigenvalue := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : ℂ)) ⟨?_, one_ne_zero⟩
    rw [Module.End.mem_eigenspace_iff]
    simp

namespace RiemannScaffold

/-- **The named hypothesis.** Every nontrivial zero of `ζ` has its Hilbert–Pólya
spectral parameter realized by a Brockian system. -/
def BrockianRealization : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → Nonempty (BrockianSystem (spectralParameter s))

/-- **Reduction theorem.** If every nontrivial zero of `ζ` admits a Brockian
system for its spectral parameter, then the Riemann Hypothesis holds. -/
theorem RH_of_BrockianSystem (hB : BrockianRealization) : RiemannHypothesis := by
  intro s hs htriv hone
  obtain ⟨B⟩ := hB s ⟨hs, htriv, hone⟩
  exact (spectralParameter_isReal_iff s).mp B.im_eq_zero

/-- The converse: the Riemann Hypothesis implies the Brockian realization
hypothesis. In particular the hypothesis is not vacuous, and is no stronger than
the Riemann Hypothesis itself. -/
theorem brockianRealization_of_RiemannHypothesis (h : RiemannHypothesis) :
    BrockianRealization := by
  intro s hs
  have hre : s.re = 1 / 2 := h s hs.1 hs.2.1 hs.2.2
  exact ⟨BrockianSystem.ofReal _ ((spectralParameter_isReal_iff s).mpr hre)⟩

/-- The named hypothesis is *equivalent* to the Riemann Hypothesis. -/
theorem brockianRealization_iff_riemannHypothesis :
    BrockianRealization ↔ RiemannHypothesis :=
  ⟨RH_of_BrockianSystem, brockianRealization_of_RiemannHypothesis⟩

end RiemannScaffold

end Brockian

