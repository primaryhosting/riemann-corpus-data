import Mathlib
/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- Complexified Minkowski spacetime: four complex coordinates. -/
abbrev Spacetime : Type := Fin 4 → ℂ

/-- The Minkowski metric `diag (1, -1, -1, -1)`, complexified. -/
noncomputable def minkowski : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- A complex matrix is a complex Lorentz transformation when it preserves the
(complex bilinear extension of the) Minkowski form. -/
def IsComplexLorentz (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  L.transpose * minkowski * L = minkowski

/-- The complex Lorentz group. -/
def ComplexLorentzGroup : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {L | IsComplexLorentz L}

/-- The total spacetime inversion `x ↦ -x` (the `PT` part of `CPT`). -/
noncomputable def cptMatrix : Matrix (Fin 4) (Fin 4) ℂ := -1

/-- A path of complex Lorentz transformations joining the identity to `-1`.
It is the product of a complex boost of rapidity `i π t` in the `(0,1)`-plane
with a rotation of angle `π t` in the `(2,3)`-plane. -/
noncomputable def cptPath (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of
    ![![(Real.cos (π * t) : ℂ), Complex.I * (Real.sin (π * t) : ℂ), 0, 0],
      ![Complex.I * (Real.sin (π * t) : ℂ), (Real.cos (π * t) : ℂ), 0, 0],
      ![0, 0, (Real.cos (π * t) : ℂ), -(Real.sin (π * t) : ℂ)],
      ![0, 0, (Real.sin (π * t) : ℂ), (Real.cos (π * t) : ℂ)]]

theorem cptPath_mem (t : ℝ) : cptPath t ∈ ComplexLorentzGroup := by
  have h : Complex.sin ((π : ℂ) * (t : ℂ)) ^ 2 + Complex.cos ((π : ℂ) * (t : ℂ)) ^ 2 = 1 :=
    Complex.sin_sq_add_cos_sq _
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  show cptPath t |>.transpose * minkowski * cptPath t = minkowski
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cptPath, minkowski, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.transpose_apply, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [hI]) <;>
    first
      | linear_combination h
      | linear_combination -h

theorem cptPath_zero : cptPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptPath]

theorem cptPath_one : cptPath 1 = cptMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptPath, cptMatrix]

theorem continuous_cptPath : Continuous cptPath := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cptPath] <;> fun_prop

/-- **Pauli–Jost lemma**: total spacetime inversion lies in the identity component of
the complex Lorentz group; i.e. it is joined to the identity by a path of complex
Lorentz transformations. This is the algebraic heart of the CPT theorem. -/
theorem cptMatrix_joined_one : JoinedIn ComplexLorentzGroup 1 cptMatrix := by
  refine ⟨⟨⟨fun t => cptPath (t : ℝ), continuous_cptPath.comp continuous_subtype_val⟩, ?_, ?_⟩,
    ?_⟩
  · simpa using cptPath_zero
  · simpa using cptPath_one
  · intro t
    exact cptPath_mem _

/-- A local, Lorentz-invariant quantum field theory, presented through its
(analytically continued) Wightman functions. -/
structure LocalQFT where
  /-- The `n`-point Wightman function, continued to complexified spacetime. -/
  W : (n : ℕ) → (Fin n → Spacetime) → ℂ
  /-- Lorentz invariance. By the Bargmann–Hall–Wightman theorem, invariance of the
  Wightman functions under the real proper orthochronous Lorentz group, together with
  the spectral condition, extends by analytic continuation to invariance under the
  identity component of the *complex* Lorentz group; this is the form assumed here. -/
  lorentz_invariant : ∀ (n : ℕ) (L : Matrix (Fin 4) (Fin 4) ℂ),
    JoinedIn ComplexLorentzGroup 1 L → ∀ x : Fin n → Spacetime,
      W n (fun i => L.mulVec (x i)) = W n x
  /-- Locality, in the form of weak local commutativity: the Wightman functions are
  invariant under reversal of their arguments. -/
  local_commutativity : ∀ (n : ℕ) (x : Fin n → Spacetime),
    W n (fun i => x i.rev) = W n x

/-- **CPT theorem**: any Lorentz-invariant local quantum field theory is CPT invariant,
i.e. its Wightman functions satisfy
`W (x₁, …, xₙ) = W (-xₙ, …, -x₁)`. -/
theorem cpt_theorem (T : LocalQFT) (n : ℕ) (x : Fin n → Spacetime) :
    T.W n (fun i => -(x i.rev)) = T.W n x := by
  have hmul : ∀ v : Spacetime, cptMatrix.mulVec v = -v := by
    intro v
    simp [cptMatrix, Matrix.neg_mulVec]
  have h1 := T.lorentz_invariant n cptMatrix cptMatrix_joined_one (fun i => x i.rev)
  simp only [hmul] at h1
  rw [h1, T.local_commutativity]

end Phys

