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

/-
# Axiom report

Building this module prints the axiom dependencies of every headline result of the
Paley–Pentagon spectral compiler.  All of them depend only on the three standard axioms of
Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`): the development contains no
unproved placeholders, no extra axioms, and no kernel-bypassing evaluation.
-/
import Brockian.PaleyPentagon

-- Target 1: the invariant decomposition.
#print axioms Brockian.PentagonLexicographic.invariant_decomposition

-- Target 2: the full normalized-Laplacian spectrum from the fibre spectrum.
#print axioms Brockian.PentagonLexicographic.full_spectrum_of_fiber_spectrum
#print axioms Brockian.PentagonLexicographic.lexAdj_spectrum

-- Target 3: the conditional compiler from `PaleySpectrumData`, and its non-vacuity.
#print axioms Brockian.PaleyPentagon.full_spectrum
#print axioms Brockian.PaleyPentagon.paleyFive

-- Target 4: the uniform spectral gap.
#print axioms Brockian.PaleyPentagon.uniform_gap

-- Supporting results: the spectrum of the pentagon and the graph-theoretic interpretation.
#print axioms Brockian.cycle5_spectrum
#print axioms Brockian.PentagonLexicographic.adjMatrix_lexProd_cycle5
#print axioms Brockian.PentagonLexicographic.adjMatrix_cycleGraph_five
#print axioms Brockian.PentagonLexicographic.lexAdj_mulVec_one_lexDegree

/-
# The Paley–Pentagon spectral compiler

Let `H` be a regular graph on `q = 2m+1` vertices with adjacency matrix `B`, of degree
`s = (q-1)/2 = m`, whose nonconstant eigenvalues are
`r = (-1+√q)/2` and `τ = (-1-√q)/2`, each of multiplicity `m = (q-1)/2`
(a *conference graph*; the Paley graphs are the standard examples).

Let `X = C₅[H]` be the lexicographic product of the pentagon with `H`, so that
`A_X = A(C₅) ⊗ J_q + I₅ ⊗ B`.  Then `X` is `D`-regular with `D = (5q-1)/2`, and this file
computes the *exact* spectrum of the normalized Laplacian `I - D⁻¹ A_X` of `X`:

| eigenvalue | multiplicity |
| --- | --- |
| `0` | `1` |
| `q(5-√5)/(5q-1)` | `2` |
| `q(5+√5)/(5q-1)` | `2` |
| `(5q-√q)/(5q-1)` | `5(q-1)/2` |
| `(5q+√q)/(5q-1)` | `5(q-1)/2` |

The proof is the "compiler" pattern: the space of functions on `V(X)` splits into
`base ⊗ constants` (where `J_q` acts as `q`, so `A_X` acts as `q·A(C₅) + s`) and
`base ⊗ constant-orthogonal` (where `J_q` acts as `0`, so `A_X` acts as `I₅ ⊗ B`), and the
dimensions of the exhibited eigenspaces already add up to `5q`, which forces them to be the
whole eigenspaces.
-/
import Brockian.Cycle5

namespace Brockian

namespace PentagonLexicographic

open Module Matrix
open scoped Kronecker

variable {V : Type*} [Fintype V]

/-! ## The lexicographic product `C₅[H]` -/

/-- The adjacency matrix `A(C₅) ⊗ J + I ⊗ B` of the lexicographic product `C₅[H]`, where `B`
is the adjacency matrix of `H`. -/
def lexAdj (B : Matrix V V ℝ) : Matrix (Fin 5 × V) (Fin 5 × V) ℝ :=
  cycle5 ⊗ₖ allOnes V ℝ + (1 : Matrix (Fin 5) (Fin 5) ℝ) ⊗ₖ B

/-- The degree `D = (5q-1)/2` of `C₅[H]` when `H` is `(q-1)/2`-regular on `q` vertices. -/
noncomputable def lexDegree (V : Type*) [Fintype V] : ℝ := (5 * Fintype.card V - 1) / 2

/-- The normalized Laplacian `I - D⁻¹ A_X` of `X = C₅[H]`. -/
noncomputable def lexNormLap [DecidableEq V] (B : Matrix V V ℝ) :
    Matrix (Fin 5 × V) (Fin 5 × V) ℝ :=
  normLap (lexDegree V) (lexAdj B)

/-- Entrywise description of the action of `A_X`: the pentagon acts on the fibre sums, and
`B` acts inside each fibre. -/
theorem lexAdj_mulVec_apply (B : Matrix V V ℝ) (F : Fin 5 × V → ℝ) (i : Fin 5) (v : V) :
    (lexAdj B *ᵥ F) (i, v)
      = (∑ j, cycle5 i j * ∑ w, F (j, w)) + (B *ᵥ fun w => F (i, w)) v := by
  simp only [lexAdj, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.add_apply,
    Matrix.kroneckerMap_apply, allOnes_apply, Matrix.one_apply, mul_one, add_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  · rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]

/-! ## The two invariant summands -/

/-- The embedding `f ↦ f ⊗ 1` of base functions as functions constant on the fibres. -/
noncomputable def kronConst (V : Type*) [Fintype V] : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 × V → ℝ) where
  toFun f := f ⊛ (fun _ => 1)
  map_add' f g := by ext p; simp [vkron]
  map_smul' c f := by ext p; simp [vkron]

@[simp] theorem kronConst_apply (V : Type*) [Fintype V] (f : Fin 5 → ℝ) (p : Fin 5 × V) :
    kronConst V f p = f p.1 := by simp [kronConst, vkron]

theorem kronConst_injective [Nonempty V] : Function.Injective (kronConst V) := by
  intro f g h
  funext i
  simpa using congrFun h (i, Classical.arbitrary V)

/-- The sum functional on the fibre. -/
noncomputable def sumLin (V : Type*) [Fintype V] : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∑ v, g v
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- The hyperplane of vectors orthogonal to the constant vector. -/
noncomputable def sumZero (V : Type*) [Fintype V] : Submodule ℝ (V → ℝ) := LinearMap.ker (sumLin V)

@[simp]
theorem mem_sumZero {g : V → ℝ} : g ∈ sumZero V ↔ ∑ v, g v = 0 := Iff.rfl

/-- `base ⊗ constants`: functions on `V(X)` that are constant on every fibre. -/
noncomputable def baseConst (V : Type*) [Fintype V] : Submodule ℝ (Fin 5 × V → ℝ) :=
  LinearMap.range (kronConst V)

/-- `base ⊗ constant-orthogonal`: functions on `V(X)` summing to zero on every fibre. -/
noncomputable def baseOrth (V : Type*) [Fintype V] : Submodule ℝ (Fin 5 × V → ℝ) :=
  fiberPow (Fin 5) (sumZero V)

section Regular

variable {B : Matrix V V ℝ} {d : ℝ}

/-- For a symmetric regular matrix, the column sums equal the degree. -/
theorem colSum_of_regular (hsymm : B.IsSymm) (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ))
    (w : V) : ∑ v, B v w = d := by
  have h := congrFun hreg w
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl fun v _ => hsymm.apply w v

/-- Summing `B *ᵥ g` over all vertices multiplies the total sum by the degree. -/
theorem sum_mulVec_of_regular (hsymm : B.IsSymm) (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ))
    (g : V → ℝ) : ∑ v, (B *ᵥ g) v = d * ∑ v, g v := by
  have : ∑ v, (B *ᵥ g) v = ∑ w, (∑ v, B v w) * g w := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [this]
  simp only [colSum_of_regular hsymm hreg]
  rw [Finset.mul_sum]

/-- An eigenvector for an eigenvalue different from the degree is orthogonal to constants. -/
theorem sum_eq_zero_of_eigenvector (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) {c : ℝ} (hc : c ≠ d) {g : V → ℝ}
    (hg : B *ᵥ g = c • g) : ∑ v, g v = 0 := by
  have h1 : c * ∑ v, g v = d * ∑ v, g v := by
    rw [← sum_mulVec_of_regular hsymm hreg g, hg]
    simp [Finset.mul_sum]
  have := sub_eq_zero.2 h1
  rw [← sub_mul] at this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hc
  · exact h

/-- `A_X` acts on `f ⊗ 1` as `q·A(C₅) + s` acts on `f`. -/
theorem lexAdj_mulVec_kronConst (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) (f : Fin 5 → ℝ) :
    lexAdj B *ᵥ (kronConst V f)
      = kronConst V ((Fintype.card V : ℝ) • (cycle5 *ᵥ f) + d • f) := by
  show lexAdj B *ᵥ (f ⊛ (fun _ => 1)) = _
  rw [lexAdj, lex_mulVec_vkron, hreg]
  ext p
  simp [vkron, Finset.card_univ, mul_comm]

/-- Eigenvectors of the pentagon give eigenvectors of `X` supported on `base ⊗ constants`. -/
theorem map_kronConst_eigenspace_le (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) (mu : ℝ) :
    (Module.End.eigenspace cycle5.mulVecLin mu).map (kronConst V)
      ≤ Module.End.eigenspace (lexAdj B).mulVecLin ((Fintype.card V : ℝ) * mu + d) := by
  rw [Submodule.map_le_iff_le_comap]
  intro f hf
  rw [Module.End.mem_eigenspace_iff] at hf
  rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff]
  simp only [Matrix.mulVecLin_apply] at hf ⊢
  rw [lexAdj_mulVec_kronConst hreg, hf]
  rw [← LinearMap.map_smul]
  congr 1
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Eigenvectors of the fibre `B` for an eigenvalue `≠ s` give eigenvectors of `X` with the
same eigenvalue, in every fibre independently. -/
theorem fiberPow_eigenspace_le (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) {c : ℝ} (hc : c ≠ d) :
    fiberPow (Fin 5) (Module.End.eigenspace B.mulVecLin c)
      ≤ Module.End.eigenspace (lexAdj B).mulVecLin c := by
  intro F hF
  rw [mem_fiberPow] at hF
  have hfib : ∀ i, B *ᵥ (fun w => F (i, w)) = c • (fun w => F (i, w)) := by
    intro i
    have := hF i
    rw [Module.End.mem_eigenspace_iff] at this
    exact this
  have hsum : ∀ i, ∑ w, F (i, w) = 0 := fun i =>
    sum_eq_zero_of_eigenvector hsymm hreg hc (hfib i)
  rw [Module.End.mem_eigenspace_iff]
  ext p
  obtain ⟨i, v⟩ := p
  simp only [Matrix.mulVecLin_apply, lexAdj_mulVec_apply, hsum, mul_zero, Finset.sum_const_zero,
    zero_add, hfib i, Pi.smul_apply, smul_eq_mul]

/-! ### Target 1: the invariant decomposition -/

/-- **The invariant decomposition.** The space of functions on `V(X)` is the direct sum of
`base ⊗ constants` and `base ⊗ constant-orthogonal`, and both summands are invariant under
the adjacency operator of `X = C₅[H]`. -/
theorem invariant_decomposition [Nonempty V] (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) :
    IsCompl (baseConst V) (baseOrth V) ∧
    (∀ F ∈ baseConst V, lexAdj B *ᵥ F ∈ baseConst V) ∧
    (∀ F ∈ baseOrth V, lexAdj B *ᵥ F ∈ baseOrth V) := by
  have hcard : (0:ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- disjointness
    rw [Submodule.disjoint_def]
    rintro F ⟨f, rfl⟩ hF
    rw [baseOrth, mem_fiberPow] at hF
    have : ∀ i, f i = 0 := by
      intro i
      have := hF i
      rw [mem_sumZero] at this
      simp only [kronConst_apply] at this
      rw [Finset.sum_const, nsmul_eq_mul] at this
      have hne : ((Finset.univ : Finset V).card : ℝ) ≠ 0 := by
        rw [Finset.card_univ]; exact_mod_cast Fintype.card_ne_zero
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hne
      · exact h
    ext p
    simp [this]
  · -- codisjointness
    rw [codisjoint_iff, eq_top_iff]
    intro F _
    set c : Fin 5 → ℝ := fun i => (∑ v, F (i, v)) / Fintype.card V with hc
    refine Submodule.mem_sup.2 ⟨kronConst V c, ⟨c, rfl⟩, F - kronConst V c, ?_, ?_⟩
    · rw [baseOrth, mem_fiberPow]
      intro i
      rw [mem_sumZero]
      simp only [Pi.sub_apply, kronConst_apply, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, hc, Finset.card_univ]
      field_simp
      ring
    · abel
  · -- invariance of the constant part
    rintro F ⟨f, rfl⟩
    exact ⟨_, (lexAdj_mulVec_kronConst hreg f).symm⟩
  · -- invariance of the orthogonal part
    intro F hF
    rw [baseOrth, mem_fiberPow] at hF ⊢
    intro i
    rw [mem_sumZero]
    have hz : ∀ j, ∑ w, F (j, w) = 0 := fun j => (mem_sumZero.1 (hF j))
    have : ∑ v, (lexAdj B *ᵥ F) (i, v)
        = ∑ v, ((∑ j, cycle5 i j * ∑ w, F (j, w)) + (B *ᵥ fun w => F (i, w)) v) :=
      Finset.sum_congr rfl fun v _ => lexAdj_mulVec_apply B F i v
    rw [this, Finset.sum_add_distrib, sum_mulVec_of_regular hsymm hreg]
    simp [hz]

end Regular

/-! ## The five eigenspaces of `X = C₅[H]` -/

section Spectrum

variable {B : Matrix V V ℝ} {m q : ℕ}

/-- The five eigenvalues of the adjacency matrix of `X = C₅[H]`, where `H` is a conference
graph on `q` vertices: `2q + s`, `qφ₊ + s`, `qφ₋ + s` (from the constant fibres) and
`(-1±√q)/2` (from the fibrewise eigenvectors), with `s = (q-1)/2`. -/
noncomputable def lexAdjEigenvalues (q : ℕ) : Fin 5 → ℝ
  | 0 => 2 * q + ((q : ℝ) - 1) / 2
  | 1 => q * phiPlus + ((q : ℝ) - 1) / 2
  | 2 => q * phiMinus + ((q : ℝ) - 1) / 2
  | 3 => (-1 + Real.sqrt q) / 2
  | 4 => (-1 - Real.sqrt q) / 2

@[simp] theorem lexAdjEigenvalues_zero :
    lexAdjEigenvalues q 0 = 2 * q + ((q : ℝ) - 1) / 2 := rfl
@[simp] theorem lexAdjEigenvalues_one :
    lexAdjEigenvalues q 1 = q * phiPlus + ((q : ℝ) - 1) / 2 := rfl
@[simp] theorem lexAdjEigenvalues_two :
    lexAdjEigenvalues q 2 = q * phiMinus + ((q : ℝ) - 1) / 2 := rfl
@[simp] theorem lexAdjEigenvalues_three :
    lexAdjEigenvalues q 3 = (-1 + Real.sqrt q) / 2 := rfl
@[simp] theorem lexAdjEigenvalues_four :
    lexAdjEigenvalues q 4 = (-1 - Real.sqrt q) / 2 := rfl

/-- The five eigenvalues of the normalized Laplacian of `X = C₅[H]`. -/
noncomputable def lexNLEigenvalues (q : ℕ) : Fin 5 → ℝ
  | 0 => 0
  | 1 => q * (5 - Real.sqrt 5) / (5 * q - 1)
  | 2 => q * (5 + Real.sqrt 5) / (5 * q - 1)
  | 3 => (5 * q - Real.sqrt q) / (5 * q - 1)
  | 4 => (5 * q + Real.sqrt q) / (5 * q - 1)

@[simp] theorem lexNLEigenvalues_zero : lexNLEigenvalues q 0 = 0 := rfl
@[simp] theorem lexNLEigenvalues_one :
    lexNLEigenvalues q 1 = q * (5 - Real.sqrt 5) / (5 * q - 1) := rfl
@[simp] theorem lexNLEigenvalues_two :
    lexNLEigenvalues q 2 = q * (5 + Real.sqrt 5) / (5 * q - 1) := rfl
@[simp] theorem lexNLEigenvalues_three :
    lexNLEigenvalues q 3 = (5 * q - Real.sqrt q) / (5 * q - 1) := rfl
@[simp] theorem lexNLEigenvalues_four :
    lexNLEigenvalues q 4 = (5 * q + Real.sqrt q) / (5 * q - 1) := rfl

/-- The multiplicities `1, 2, 2, 5(q-1)/2, 5(q-1)/2` (with `m = (q-1)/2`). -/
def lexMultiplicities (m : ℕ) : Fin 5 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 5 * m
  | 4 => 5 * m

@[simp] theorem lexMultiplicities_zero : lexMultiplicities m 0 = 1 := rfl
@[simp] theorem lexMultiplicities_one : lexMultiplicities m 1 = 2 := rfl
@[simp] theorem lexMultiplicities_two : lexMultiplicities m 2 = 2 := rfl
@[simp] theorem lexMultiplicities_three : lexMultiplicities m 3 = 5 * m := rfl
@[simp] theorem lexMultiplicities_four : lexMultiplicities m 4 = 5 * m := rfl

/-- The five eigenspaces of `X = C₅[H]`: three copies of pentagon eigenspaces sitting inside
`base ⊗ constants`, and two fibrewise eigenspaces inside `base ⊗ constant-orthogonal`. -/
noncomputable def lexSpaces (B : Matrix V V ℝ) (q : ℕ) : Fin 5 → Submodule ℝ (Fin 5 × V → ℝ)
  | 0 => cyc5Const.map (kronConst V)
  | 1 => (cyc5Eig phiPlus).map (kronConst V)
  | 2 => (cyc5Eig phiMinus).map (kronConst V)
  | 3 => fiberPow (Fin 5) (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2))
  | 4 => fiberPow (Fin 5) (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2))

@[simp]
theorem lexSpaces_zero : lexSpaces B q 0 = cyc5Const.map (kronConst V) := rfl
@[simp]
theorem lexSpaces_one : lexSpaces B q 1 = (cyc5Eig phiPlus).map (kronConst V) := rfl
@[simp]
theorem lexSpaces_two : lexSpaces B q 2 = (cyc5Eig phiMinus).map (kronConst V) := rfl
@[simp]
theorem lexSpaces_three : lexSpaces B q 3 =
    fiberPow (Fin 5) (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) := rfl
@[simp]
theorem lexSpaces_four : lexSpaces B q 4 =
    fiberPow (Fin 5) (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) := rfl

/-! ### Numerical facts about `√q` -/

theorem sqrtq_sq (q : ℕ) : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by positivity)

theorem two_lt_sqrtq (hm : 2 ≤ m) (hq : q = 2 * m + 1) : 2 < Real.sqrt q := by
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h5 : (5 : ℝ) ≤ q := by rw [hq]; push_cast; linarith
  nlinarith [sqrtq_sq q, Real.sqrt_nonneg (q : ℝ)]

theorem two_sqrtq_lt (hm : 2 ≤ m) (hq : q = 2 * m + 1) : 2 * Real.sqrt q < q := by
  nlinarith [sqrtq_sq q, two_lt_sqrtq hm hq]

/-- The five adjacency eigenvalues are ordered `λ₂ < λ₄ < 0 < λ₃ < λ₁ < λ₀`. -/
theorem lexAdjEigenvalues_chain (hm : 2 ≤ m) (hq : q = 2 * m + 1) :
    lexAdjEigenvalues q 2 < lexAdjEigenvalues q 4 ∧
    lexAdjEigenvalues q 4 < 0 ∧
    (0 : ℝ) < lexAdjEigenvalues q 3 ∧
    lexAdjEigenvalues q 3 < lexAdjEigenvalues q 1 ∧
    lexAdjEigenvalues q 1 < lexAdjEigenvalues q 0 := by
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hqr : (q : ℝ) = 2 * m + 1 := by rw [hq]; push_cast; ring
  have h1 := two_lt_sqrtq hm hq
  have h2 := two_sqrtq_lt hm hq
  have hp := phiPlus_bounds
  have hn := phiMinus_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [lexAdjEigenvalues_zero, lexAdjEigenvalues_one,
    lexAdjEigenvalues_two, lexAdjEigenvalues_three, lexAdjEigenvalues_four] <;> nlinarith [hp.1, hp.2, hn.1, hn.2]

theorem lexAdjEigenvalues_injective (hm : 2 ≤ m) (hq : q = 2 * m + 1) :
    Function.Injective (lexAdjEigenvalues q) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := lexAdjEigenvalues_chain hm hq
  have hne1 : phiPlus ≠ phiMinus := by
    intro h
    have h1 := phiPlus_bounds.1
    have h2 := phiMinus_bounds.2
    rw [h] at h1
    linarith
  have hne2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

/-! ### The eigenvector containments -/

variable {d : ℝ}

theorem map_kronConst_le_of_le (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ))
    {mu : ℝ} {C : Submodule ℝ (Fin 5 → ℝ)} (hC : C ≤ Module.End.eigenspace cycle5.mulVecLin mu)
    {lam : ℝ} (hlam : (Fintype.card V : ℝ) * mu + d = lam) :
    C.map (kronConst V) ≤ Module.End.eigenspace (lexAdj B).mulVecLin lam :=
  hlam ▸ le_trans (Submodule.map_mono hC) (map_kronConst_eigenspace_le hreg mu)

theorem lexSpaces_le (hm : 2 ≤ m) (hq : q = 2 * m + 1) (hcard : Fintype.card V = q)
    (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ)) (i : Fin 5) :
    lexSpaces B q i ≤ Module.End.eigenspace (lexAdj B).mulVecLin (lexAdjEigenvalues q i) := by
  have hcardr : (Fintype.card V : ℝ) = q := by rw [hcard]
  have h1 := two_lt_sqrtq hm hq
  have h2 := two_sqrtq_lt hm hq
  fin_cases i
  · exact map_kronConst_le_of_le hreg cyc5Const_le_eigenspace (by rw [hcardr]; simp; ring)
  · exact map_kronConst_le_of_le hreg (cyc5Eig_le_eigenspace phiPlus_sq) (by rw [hcardr]; simp)
  · exact map_kronConst_le_of_le hreg (cyc5Eig_le_eigenspace phiMinus_sq) (by rw [hcardr]; simp)
  · exact fiberPow_eigenspace_le hsymm hreg (by intro h; rw [div_eq_div_iff] at h <;> nlinarith)
  · exact fiberPow_eigenspace_le hsymm hreg (by intro h; rw [div_eq_div_iff] at h <;> nlinarith)

/-! ### The dimension count -/

theorem finrank_map_kronConst [Nonempty V] (P : Submodule ℝ (Fin 5 → ℝ)) :
    finrank ℝ (P.map (kronConst V)) = finrank ℝ P :=
  ((Submodule.equivMapOfInjective (kronConst V) kronConst_injective P).finrank_eq).symm

theorem lexSpaces_finrank [Nonempty V]
    (hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m)
    (ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m) (i : Fin 5) :
    finrank ℝ (lexSpaces B q i) = lexMultiplicities m i := by
  fin_cases i
  · show finrank ℝ (lexSpaces B q 0) = lexMultiplicities m 0
    rw [lexSpaces_zero, finrank_map_kronConst, finrank_cyc5Const]; rfl
  · show finrank ℝ (lexSpaces B q 1) = lexMultiplicities m 1
    rw [lexSpaces_one, finrank_map_kronConst, finrank_cyc5Eig phiPlus_ne_zero]; rfl
  · show finrank ℝ (lexSpaces B q 2) = lexMultiplicities m 2
    rw [lexSpaces_two, finrank_map_kronConst, finrank_cyc5Eig phiMinus_ne_zero]; rfl
  · show finrank ℝ (lexSpaces B q 3) = lexMultiplicities m 3
    rw [lexSpaces_three, finrank_fiberPow, hr]; simp
  · show finrank ℝ (lexSpaces B q 4) = lexMultiplicities m 4
    rw [lexSpaces_four, finrank_fiberPow, ht]; simp

theorem lexSpaces_finrank_sum [Nonempty V] (hq : q = 2 * m + 1) (hcard : Fintype.card V = q)
    (hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m)
    (ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m) :
    ∑ i, finrank ℝ (lexSpaces B q i) = finrank ℝ (Fin 5 × V → ℝ) := by
  rw [Fin.sum_univ_five]
  simp only [lexSpaces_finrank hr ht, lexMultiplicities_zero, lexMultiplicities_one,
    lexMultiplicities_two, lexMultiplicities_three, lexMultiplicities_four]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, hcard, hq]
  ring

/-! ### Target 2: the full spectrum -/

/-- The exact spectrum of the **adjacency matrix** of `X = C₅[H]`. -/
theorem lexAdj_spectrum [Nonempty V] (hm : 2 ≤ m) (hq : q = 2 * m + 1)
    (hcard : Fintype.card V = q) (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ))
    (hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m)
    (ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m) :
    (⨆ i, Module.End.eigenspace (lexAdj B).mulVecLin (lexAdjEigenvalues q i)) = ⊤ ∧
    ∀ i, Module.End.eigenspace (lexAdj B).mulVecLin (lexAdjEigenvalues q i) = lexSpaces B q i :=
  eigenspace_eq_of_finrank_sum _ _ (lexAdjEigenvalues_injective hm hq) _
    (lexSpaces_le hm hq hcard hsymm hreg) (lexSpaces_finrank_sum hq hcard hr ht)

theorem lexDegree_eq (hcard : Fintype.card V = q) :
    lexDegree V = (5 * (q : ℝ) - 1) / 2 := by
  rw [lexDegree, hcard]

theorem lexDegree_ne_zero (hm : 2 ≤ m) (hq : q = 2 * m + 1) (hcard : Fintype.card V = q) :
    lexDegree V ≠ 0 := by
  rw [lexDegree_eq hcard, hq]
  have : (2:ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  intro h
  nlinarith

/-- The five normalized-Laplacian eigenvalues are `1 - λ/D` for the five adjacency
eigenvalues `λ`. -/
theorem lexNLEigenvalues_eq (hm : 2 ≤ m) (hq : q = 2 * m + 1) (hcard : Fintype.card V = q)
    (i : Fin 5) :
    lexNLEigenvalues q i = 1 - lexAdjEigenvalues q i / lexDegree (V := V) := by
  have hD : lexDegree (V := V) = (5 * (q : ℝ) - 1) / 2 := lexDegree_eq hcard
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq5 : (5 : ℝ) ≤ q := by rw [hq]; push_cast; linarith
  have hDne : (5 * (q : ℝ) - 1) ≠ 0 := by intro h; nlinarith
  fin_cases i
  · show lexNLEigenvalues q 0 = 1 - lexAdjEigenvalues q 0 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_zero, lexAdjEigenvalues_zero, eq_comm, sub_eq_zero, eq_comm,
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 1 = 1 - lexAdjEigenvalues q 1 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_one, lexAdjEigenvalues_one, phiPlus, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 2 = 1 - lexAdjEigenvalues q 2 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_two, lexAdjEigenvalues_two, phiMinus, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 3 = 1 - lexAdjEigenvalues q 3 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_three, lexAdjEigenvalues_three, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring
  · show lexNLEigenvalues q 4 = 1 - lexAdjEigenvalues q 4 / lexDegree (V := V)
    rw [hD, lexNLEigenvalues_four, lexAdjEigenvalues_four, eq_sub_iff_add_eq,
      div_add_div _ _ (by intro h; nlinarith) (by intro h; nlinarith),
      div_eq_one_iff_eq (by intro h; nlinarith)]
    ring

theorem eigenspace_lexNormLap [DecidableEq V] (hm : 2 ≤ m) (hq : q = 2 * m + 1) (hcard : Fintype.card V = q)
    (i : Fin 5) :
    Module.End.eigenspace (lexNormLap B).mulVecLin (lexNLEigenvalues q i)
      = Module.End.eigenspace (lexAdj B).mulVecLin (lexAdjEigenvalues q i) := by
  rw [lexNLEigenvalues_eq hm hq hcard i, lexNormLap]
  exact eigenspace_normLap _ (lexDegree_ne_zero hm hq hcard) _ _

/-- **The full normalized-Laplacian spectrum of `X = C₅[H]`.**

If `H` is a symmetric `(q-1)/2`-regular graph on `q = 2m+1` vertices whose eigenvalues
`(-1±√q)/2` each have multiplicity `m = (q-1)/2` (a conference graph, e.g. a Paley graph),
then the normalized Laplacian of the lexicographic product `X = C₅[H]` has spectrum

* `0` with multiplicity `1`,
* `q(5-√5)/(5q-1)` with multiplicity `2`,
* `q(5+√5)/(5q-1)` with multiplicity `2`,
* `(5q-√q)/(5q-1)` with multiplicity `5(q-1)/2 = 5m`,
* `(5q+√q)/(5q-1)` with multiplicity `5(q-1)/2 = 5m`,

and these five eigenspaces span the whole `5q`-dimensional space. -/
theorem full_spectrum_of_fiber_spectrum [DecidableEq V] [Nonempty V] (hm : 2 ≤ m) (hq : q = 2 * m + 1)
    (hcard : Fintype.card V = q) (hsymm : B.IsSymm)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ))
    (hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m)
    (ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m) :
    (⨆ i, Module.End.eigenspace (lexNormLap B).mulVecLin (lexNLEigenvalues q i)) = ⊤ ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin 0) = 1 ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((q : ℝ) * (5 - Real.sqrt 5) / (5 * q - 1))) = 2 ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((q : ℝ) * (5 + Real.sqrt 5) / (5 * q - 1))) = 2 ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((5 * (q : ℝ) - Real.sqrt q) / (5 * q - 1))) = 5 * m ∧
    finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      ((5 * (q : ℝ) + Real.sqrt q) / (5 * q - 1))) = 5 * m := by
  obtain ⟨htop, heq⟩ := lexAdj_spectrum hm hq hcard hsymm hreg hr ht
  have key : ∀ i, finrank ℝ (Module.End.eigenspace (lexNormLap B).mulVecLin
      (lexNLEigenvalues q i)) = lexMultiplicities m i := by
    intro i
    rw [eigenspace_lexNormLap hm hq hcard i, heq i]
    exact lexSpaces_finrank hr ht i
  refine ⟨?_, key 0, key 1, key 2, key 3, key 4⟩
  simp only [eigenspace_lexNormLap hm hq hcard]
  exact htop

end Spectrum

end PentagonLexicographic

/-! # The conditional Paley compiler

`PaleySpectrumData` packages exactly what the compiler needs about the fibre graph `H`:
it is a symmetric `(q-1)/2`-regular graph on `q = 2m+1` vertices whose two nonprincipal
eigenvalues `(-1±√q)/2` have multiplicity `m` each, together with the invariant
decomposition of the function space of `X = C₅[H]`.
-/

namespace PaleyPentagon

open Module Matrix PentagonLexicographic

/-- The input data of the Paley–Pentagon spectral compiler: a *conference graph* `H`
(a symmetric `(q-1)/2`-regular graph on `q = 2m+1 ≥ 5` vertices whose nonprincipal
eigenvalues are `(-1±√q)/2`, each with multiplicity `m = (q-1)/2`), together with the
invariant decomposition of the function space of the lexicographic product `C₅[H]`.

The Paley graphs of prime-power order `q ≡ 1 mod 4` are the motivating family; the
structure is non-vacuous: see `PaleyPentagon.paleyFive`, the Paley graph of order `5`
(which is the pentagon itself). -/
structure PaleySpectrumData where
  /-- The number of vertices of the fibre graph `H`. -/
  q : ℕ
  /-- The common multiplicity `m = (q-1)/2` of the two nonprincipal eigenvalues. -/
  m : ℕ
  hq : q = 2 * m + 1
  hm : 2 ≤ m
  /-- The vertex set of `H`. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  hcard : Fintype.card V = q
  /-- The adjacency matrix of `H`. -/
  B : Matrix V V ℝ
  hsymm : B.IsSymm
  /-- `H` is `(q-1)/2`-regular. -/
  hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ)
  /-- The eigenvalue `(-1+√q)/2` has multiplicity `m`. -/
  hr : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 + Real.sqrt q) / 2)) = m
  /-- The eigenvalue `(-1-√q)/2` has multiplicity `m`. -/
  ht : finrank ℝ (Module.End.eigenspace B.mulVecLin ((-1 - Real.sqrt q) / 2)) = m
  /-- The invariant decomposition of the function space of `C₅[H]`. -/
  invariant : IsCompl (baseConst V) (baseOrth V) ∧
      (∀ F ∈ baseConst V, lexAdj B *ᵥ F ∈ baseConst V) ∧
      (∀ F ∈ baseOrth V, lexAdj B *ᵥ F ∈ baseOrth V)

attribute [instance] PaleySpectrumData.fintypeV PaleySpectrumData.decEqV

namespace PaleySpectrumData

variable (P : PaleySpectrumData)

theorem nonempty : Nonempty P.V :=
  Fintype.card_pos_iff.1 (by rw [P.hcard, P.hq]; omega)

theorem five_le_q : 5 ≤ P.q := by
  have := P.hm; have := P.hq; omega

/-- The normalized Laplacian of the compiled graph `X = C₅[H]`. -/
noncomputable def normLapX : Matrix (Fin 5 × P.V) (Fin 5 × P.V) ℝ := lexNormLap P.B

end PaleySpectrumData

/-- **The Paley–Pentagon compiler.**  From `PaleySpectrumData` for a conference graph `H` on
`q = 2m+1` vertices, the normalized Laplacian of `X = C₅[H]` has spectrum

* `0` with multiplicity `1`,
* `q(5-√5)/(5q-1)` with multiplicity `2`,
* `q(5+√5)/(5q-1)` with multiplicity `2`,
* `(5q-√q)/(5q-1)` with multiplicity `5(q-1)/2`,
* `(5q+√q)/(5q-1)` with multiplicity `5(q-1)/2`,

and the five eigenspaces span the whole `5q`-dimensional space. -/
theorem full_spectrum (P : PaleySpectrumData) :
    (⨆ i, Module.End.eigenspace P.normLapX.mulVecLin (lexNLEigenvalues P.q i)) = ⊤ ∧
    finrank ℝ (Module.End.eigenspace P.normLapX.mulVecLin 0) = 1 ∧
    finrank ℝ (Module.End.eigenspace P.normLapX.mulVecLin
      ((P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1))) = 2 ∧
    finrank ℝ (Module.End.eigenspace P.normLapX.mulVecLin
      ((P.q : ℝ) * (5 + Real.sqrt 5) / (5 * P.q - 1))) = 2 ∧
    finrank ℝ (Module.End.eigenspace P.normLapX.mulVecLin
      ((5 * (P.q : ℝ) - Real.sqrt P.q) / (5 * P.q - 1))) = 5 * P.m ∧
    finrank ℝ (Module.End.eigenspace P.normLapX.mulVecLin
      ((5 * (P.q : ℝ) + Real.sqrt P.q) / (5 * P.q - 1))) = 5 * P.m :=
  haveI := P.nonempty
  full_spectrum_of_fiber_spectrum P.hm P.hq P.hcard P.hsymm P.hreg P.hr P.ht

/-! ### Target 4: the uniform spectral gap -/

section Gap

variable (P : PaleySpectrumData)

private theorem sqrt5_facts : 2.23 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.24 := sqrt5_bounds

private theorem qpos : (5 : ℝ) ≤ P.q := by exact_mod_cast P.five_le_q

private theorem denom_pos : (0 : ℝ) < 5 * P.q - 1 := by
  have := qpos P; linarith

/-- **The uniform spectral gap.**  The spectral gap of `X = C₅[H]` (the least nonzero
eigenvalue of its normalized Laplacian) is exactly `q(5-√5)/(5q-1)`, and this is strictly
larger than the `q`-independent constant `(5-√5)/5`. -/
theorem uniform_gap :
    IsLeast {nu : ℝ | nu ≠ 0 ∧ Module.End.HasEigenvalue P.normLapX.mulVecLin nu}
      ((P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1)) ∧
    (5 - Real.sqrt 5) / 5 < (P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1) := by
  obtain ⟨htop, h0, h1, h2, h3, h4⟩ := full_spectrum P
  have hq5 := qpos P
  have hD := denom_pos P
  have hs5 := sqrt5_facts
  have hsq : Real.sqrt P.q ^ 2 = P.q := PentagonLexicographic.sqrtq_sq P.q
  have hsq2 : 2 < Real.sqrt P.q := PentagonLexicographic.two_lt_sqrtq P.hm P.hq
  have hsqq : 2 * Real.sqrt P.q < P.q := PentagonLexicographic.two_sqrtq_lt P.hm P.hq
  have hnum : (0 : ℝ) < 5 - Real.sqrt 5 := by linarith [hs5.2]
  have hgap_pos : (0 : ℝ) < (P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1) := by
    apply div_pos _ hD
    nlinarith
  refine ⟨⟨⟨ne_of_gt hgap_pos, ?_⟩, ?_⟩, ?_⟩
  · -- it really is an eigenvalue
    intro hbot
    have hz : finrank ℝ (Module.End.eigenspace P.normLapX.mulVecLin
        ((P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1))) = 0 := Submodule.finrank_eq_zero.2 hbot
    rw [h1] at hz
    exact absurd hz (by norm_num)
  · -- it is a lower bound for all nonzero eigenvalues
    rintro nu ⟨hne, hev⟩
    obtain ⟨i, rfl⟩ := eigenvalue_mem_of_iSup_eq_top _ _ htop hev
    fin_cases i
    · exact absurd rfl hne
    · exact le_rfl
    · show (P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1)
        ≤ (P.q : ℝ) * (5 + Real.sqrt 5) / (5 * P.q - 1)
      rw [div_le_div_iff_of_pos_right hD]
      nlinarith [hs5.1]
    · show (P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1)
        ≤ (5 * (P.q : ℝ) - Real.sqrt P.q) / (5 * P.q - 1)
      rw [div_le_div_iff_of_pos_right hD]
      nlinarith [hs5.1]
    · show (P.q : ℝ) * (5 - Real.sqrt 5) / (5 * P.q - 1)
        ≤ (5 * (P.q : ℝ) + Real.sqrt P.q) / (5 * P.q - 1)
      rw [div_le_div_iff_of_pos_right hD]
      nlinarith [hs5.1]
  · -- the uniform lower bound
    rw [div_lt_div_iff₀ (by norm_num) hD]
    nlinarith

end Gap

/-! ### Non-vacuity: the Paley graph of order 5 -/

/-- The pentagon `C₅` *is* the Paley graph of order `5`; it gives an instance of
`PaleySpectrumData`, so the compiler is not vacuous.  The compiled graph is `C₅[C₅]`, a
`12`-regular graph on `25` vertices. -/
noncomputable def paleyFive : PaleySpectrumData where
  q := 5
  m := 2
  hq := rfl
  hm := le_refl 2
  V := Fin 5
  hcard := by simp
  B := cycle5
  hsymm := cycle5_isSymm
  hreg := by rw [cycle5_mulVec_one]; norm_num
  hr := by
    rw [show ((5:ℕ) : ℝ) = 5 by norm_num]
    exact finrank_eigenspace_cycle5_phiPlus
  ht := by
    rw [show ((5:ℕ) : ℝ) = 5 by norm_num]
    exact finrank_eigenspace_cycle5_phiMinus
  invariant := invariant_decomposition cycle5_isSymm (by rw [cycle5_mulVec_one])

/-! ### Future target: the Paley instantiation for general prime powers

Instantiating `PaleySpectrumData` from the quadratic-character description of the Paley
graph of an arbitrary finite field of order `q ≡ 1 mod 4` needs the character-sum
computation of the eigenvalues of the Paley graph, which is not available in Mathlib at
the time of writing.  The statement of that missing input is recorded below as a
*definition of a proposition*.  It is deliberately **not** assumed anywhere: nothing in
this file depends on it, and no axiom is introduced. -/

open scoped Classical in
/-- **Future target** (not proved here, and not assumed anywhere): every finite field of
order `q ≡ 1 mod 4` gives rise to `PaleySpectrumData` whose fibre graph is the Paley graph
of that field, i.e. the graph on the field in which `x ~ y` iff `x - y` is a nonzero
square. -/
def PaleyInstantiationTarget : Prop :=
  ∀ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F % 4 = 1 → 5 ≤ Fintype.card F →
    ∃ P : PaleySpectrumData, ∃ e : P.V ≃ F, P.q = Fintype.card F ∧
      ∀ x y : P.V, P.B x y = if x ≠ y ∧ ∃ z : F, z ≠ 0 ∧ z * z = e x - e y then 1 else 0

end PaleyPentagon

/-! ## Graph-theoretic interpretation

Everything above is stated for matrices.  This section checks that `lexAdj` really is the
adjacency matrix of the lexicographic product `C₅[H]` of simple graphs, that `cycle5` is
the adjacency matrix of the pentagon, and that `lexDegree` really is the degree of `C₅[H]`.
-/

namespace PentagonLexicographic

open Matrix SimpleGraph
open scoped Kronecker

/-- The lexicographic product `G[H]`: vertices are pairs, and `(a,b) ~ (c,d)` iff `a ~ c`
in `G`, or `a = c` and `b ~ d` in `H`. -/
def lexProd {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj p r := G.Adj p.1 r.1 ∨ (p.1 = r.1 ∧ H.Adj p.2 r.2)
  symm := by
    rintro ⟨a, b⟩ ⟨c, d⟩ (h | ⟨h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  loopless := ⟨by rintro ⟨a, b⟩ (h | ⟨-, h⟩) <;> simp at h⟩

instance instDecidableRelLexProdAdj {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableEq α] [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (lexProd G H).Adj :=
  fun p r => inferInstanceAs (Decidable (G.Adj p.1 r.1 ∨ (p.1 = r.1 ∧ H.Adj p.2 r.2)))

/-- `cycle5` is the adjacency matrix of the pentagon. -/
theorem adjMatrix_cycleGraph_five : (SimpleGraph.cycleGraph 5).adjMatrix ℝ = cycle5 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SimpleGraph.adjMatrix_apply, cycle5] <;> decide

/-- `lexAdj` is the adjacency matrix of the lexicographic product `C₅[H]`. -/
theorem adjMatrix_lexProd_cycle5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] :
    (lexProd (SimpleGraph.cycleGraph 5) H).adjMatrix ℝ = lexAdj (H.adjMatrix ℝ) := by
  ext p r
  obtain ⟨i, v⟩ := p
  obtain ⟨j, w⟩ := r
  simp only [lexAdj, Matrix.add_apply, Matrix.kroneckerMap_apply, allOnes_apply,
    SimpleGraph.adjMatrix_apply, Matrix.one_apply, mul_one, lexProd]
  fin_cases i <;> fin_cases j <;> simp [cycle5] <;> decide

variable {V : Type*} [Fintype V] {B : Matrix V V ℝ} {d : ℝ}

/-- If `H` is `d`-regular then `C₅[H]` is `(2q + d)`-regular, `q = |V(H)|`. -/
theorem lexAdj_mulVec_one (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = d • (fun _ => 1 : V → ℝ)) :
    lexAdj B *ᵥ (fun _ => 1 : Fin 5 × V → ℝ)
      = (2 * (Fintype.card V : ℝ) + d) • (fun _ => 1 : Fin 5 × V → ℝ) := by
  have h : (fun _ => 1 : Fin 5 × V → ℝ) = (fun _ => 1 : Fin 5 → ℝ) ⊛ (fun _ => 1 : V → ℝ) := by
    ext p; simp [vkron]
  rw [h, show ((fun _ => 1 : Fin 5 → ℝ) ⊛ (fun _ => 1 : V → ℝ))
      = kronConst V (fun _ => 1) from rfl, lexAdj_mulVec_kronConst hreg, cycle5_mulVec_one]
  ext p
  simp [kronConst, vkron]
  ring

/-- With `H` a conference graph on `q` vertices, `C₅[H]` is `(5q-1)/2`-regular, which is the
degree `lexDegree` used to normalize the Laplacian. -/
theorem lexAdj_mulVec_one_lexDegree [DecidableEq V] {q : ℕ} (hcard : Fintype.card V = q)
    (hreg : B *ᵥ (fun _ => 1 : V → ℝ) = (((q : ℝ) - 1) / 2) • (fun _ => 1 : V → ℝ)) :
    lexAdj B *ᵥ (fun _ => 1 : Fin 5 × V → ℝ)
      = lexDegree V • (fun _ => 1 : Fin 5 × V → ℝ) := by
  rw [lexAdj_mulVec_one hreg, lexDegree, hcard]
  congr 1
  ring

end PentagonLexicographic

end Brockian

/-
# The pentagon `C₅`

The adjacency matrix of the 5-cycle, its three eigenvalues `2`, `(-1+√5)/2`, `(-1-√5)/2`
with multiplicities `1, 2, 2`, and explicit eigenvectors for each.

The eigenvectors are chosen algebraically (no trigonometry): if `a² = 1 - a`, i.e. `a` is
one of `(-1±√5)/2`, then
`vA a = (0, 1, a, -a, -1)` and `vS a = (-2a, a-1, 1, 1, a-1)`
are independent `a`-eigenvectors of the cycle.
-/
import Brockian.SpectralTools

namespace Brockian

open Module Matrix

/-- The adjacency matrix of the pentagon `C₅`. -/
def cycle5 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,1,0,0,1; 1,0,1,0,0; 0,1,0,1,0; 0,0,1,0,1; 1,0,0,1,0]

theorem cycle5_isSymm : cycle5.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `C₅` is 2-regular. -/
theorem cycle5_mulVec_one : cycle5 *ᵥ (fun _ => (1:ℝ)) = (2:ℝ) • (fun _ => (1:ℝ)) := by
  ext i
  fin_cases i <;>
    simp [cycle5, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> norm_num

/-! ### The golden eigenvalues -/

/-- `(-1+√5)/2`, the second largest eigenvalue of `C₅`. -/
noncomputable def phiPlus : ℝ := (-1 + Real.sqrt 5) / 2

/-- `(-1-√5)/2`, the smallest eigenvalue of `C₅`. -/
noncomputable def phiMinus : ℝ := (-1 - Real.sqrt 5) / 2

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_bounds : 2.23 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.24 := by
  constructor
  · nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]
  · nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

theorem phiPlus_sq : phiPlus ^ 2 = 1 - phiPlus := by
  unfold phiPlus; nlinarith [sqrt5_sq]

theorem phiMinus_sq : phiMinus ^ 2 = 1 - phiMinus := by
  unfold phiMinus; nlinarith [sqrt5_sq]

theorem phiPlus_bounds : 0.6 < phiPlus ∧ phiPlus < 0.62 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold phiPlus; constructor <;> linarith

theorem phiMinus_bounds : -1.62 < phiMinus ∧ phiMinus < -1.61 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold phiMinus; constructor <;> linarith

theorem phiPlus_ne_zero : phiPlus ≠ 0 := by
  have := phiPlus_bounds.1; intro h; rw [h] at this; norm_num at this

theorem phiMinus_ne_zero : phiMinus ≠ 0 := by
  have := phiMinus_bounds.2; intro h; rw [h] at this; norm_num at this

/-! ### Explicit eigenvectors -/

/-- The antisymmetric eigenvector `(0, 1, a, -a, -1)`. -/
def cyc5vecA (a : ℝ) : Fin 5 → ℝ := ![0, 1, a, -a, -1]

/-- The symmetric eigenvector `(-2a, a-1, 1, 1, a-1)`. -/
def cyc5vecS (a : ℝ) : Fin 5 → ℝ := ![-2*a, a-1, 1, 1, a-1]

theorem cycle5_mulVec_vecA {a : ℝ} (ha : a ^ 2 = 1 - a) :
    cycle5 *ᵥ cyc5vecA a = a • cyc5vecA a := by
  ext i
  fin_cases i <;>
    simp [cycle5, cyc5vecA, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> nlinarith [ha]

theorem cycle5_mulVec_vecS {a : ℝ} (ha : a ^ 2 = 1 - a) :
    cycle5 *ᵥ cyc5vecS a = a • cyc5vecS a := by
  ext i
  fin_cases i <;>
    simp [cycle5, cyc5vecS, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> nlinarith [ha]

theorem cyc5_linearIndependent {a : ℝ} (ha : a ≠ 0) :
    LinearIndependent ℝ ![cyc5vecA a, cyc5vecS a] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrFun hst 0
  have h1 := congrFun hst 1
  simp [cyc5vecA, cyc5vecS] at h0 h1
  have ht : t = 0 := h0.resolve_right ha
  subst ht
  simp at h1
  exact ⟨h1, rfl⟩

/-- The 2-dimensional eigenspace of `C₅` attached to a root `a` of `x² + x - 1`. -/
noncomputable def cyc5Eig (a : ℝ) : Submodule ℝ (Fin 5 → ℝ) :=
  Submodule.span ℝ (Set.range ![cyc5vecA a, cyc5vecS a])

/-- The line of constant vectors. -/
noncomputable def cyc5Const : Submodule ℝ (Fin 5 → ℝ) := ℝ ∙ (fun _ => (1:ℝ))

theorem finrank_cyc5Eig {a : ℝ} (ha : a ≠ 0) : finrank ℝ (cyc5Eig a) = 2 := by
  rw [cyc5Eig, finrank_span_eq_card (cyc5_linearIndependent ha)]
  simp

theorem finrank_cyc5Const : finrank ℝ cyc5Const = 1 := by
  refine finrank_span_singleton ?_
  intro h
  have := congrFun h 0
  norm_num at this

theorem cyc5Eig_le_eigenspace {a : ℝ} (ha : a ^ 2 = 1 - a) :
    cyc5Eig a ≤ Module.End.eigenspace cycle5.mulVecLin a := by
  rw [cyc5Eig, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact Module.End.mem_eigenspace_iff.2 (cycle5_mulVec_vecA ha)
  · exact Module.End.mem_eigenspace_iff.2 (cycle5_mulVec_vecS ha)

theorem cyc5Const_le_eigenspace :
    cyc5Const ≤ Module.End.eigenspace cycle5.mulVecLin 2 := by
  rw [cyc5Const, Submodule.span_singleton_le_iff_mem]
  exact Module.End.mem_eigenspace_iff.2 cycle5_mulVec_one

/-! ### The exact spectrum of `C₅` -/

/-- The three eigenvalues of `C₅`. -/
noncomputable def cyc5Eigenvalues : Fin 3 → ℝ
  | 0 => 2
  | 1 => phiPlus
  | 2 => phiMinus

@[simp] theorem cyc5Eigenvalues_zero : cyc5Eigenvalues 0 = 2 := rfl
@[simp] theorem cyc5Eigenvalues_one : cyc5Eigenvalues 1 = phiPlus := rfl
@[simp] theorem cyc5Eigenvalues_two : cyc5Eigenvalues 2 = phiMinus := rfl

/-- The three eigenspaces of `C₅` (as spans of the explicit eigenvectors). -/
noncomputable def cyc5Spaces : Fin 3 → Submodule ℝ (Fin 5 → ℝ)
  | 0 => cyc5Const
  | 1 => cyc5Eig phiPlus
  | 2 => cyc5Eig phiMinus

@[simp] theorem cyc5Spaces_zero : cyc5Spaces 0 = cyc5Const := rfl
@[simp] theorem cyc5Spaces_one : cyc5Spaces 1 = cyc5Eig phiPlus := rfl
@[simp] theorem cyc5Spaces_two : cyc5Spaces 2 = cyc5Eig phiMinus := rfl

theorem cyc5Eigenvalues_injective : Function.Injective cyc5Eigenvalues := by
  have hp := phiPlus_bounds
  have hm := phiMinus_bounds
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith [hp.1, hp.2, hm.1, hm.2]

theorem cyc5Spaces_le (i : Fin 3) :
    cyc5Spaces i ≤ Module.End.eigenspace cycle5.mulVecLin (cyc5Eigenvalues i) := by
  fin_cases i
  · exact cyc5Const_le_eigenspace
  · exact cyc5Eig_le_eigenspace phiPlus_sq
  · exact cyc5Eig_le_eigenspace phiMinus_sq

theorem cyc5Spaces_finrank_sum :
    ∑ i, finrank ℝ (cyc5Spaces i) = finrank ℝ (Fin 5 → ℝ) := by
  rw [Fin.sum_univ_three]
  simp only [cyc5Spaces_zero, cyc5Spaces_one, cyc5Spaces_two]
  rw [finrank_cyc5Const, finrank_cyc5Eig phiPlus_ne_zero, finrank_cyc5Eig phiMinus_ne_zero]
  simp

/-- **The spectrum of the pentagon.** The eigenvalues of `C₅` are `2` (multiplicity 1),
`(-1+√5)/2` (multiplicity 2) and `(-1-√5)/2` (multiplicity 2), and the corresponding
eigenspaces are spanned by the explicit vectors above. -/
theorem cycle5_spectrum :
    (⨆ i, Module.End.eigenspace cycle5.mulVecLin (cyc5Eigenvalues i)) = ⊤ ∧
    ∀ i, Module.End.eigenspace cycle5.mulVecLin (cyc5Eigenvalues i) = cyc5Spaces i :=
  eigenspace_eq_of_finrank_sum _ _ cyc5Eigenvalues_injective _ cyc5Spaces_le
    cyc5Spaces_finrank_sum

theorem finrank_eigenspace_cycle5_phiPlus :
    finrank ℝ (Module.End.eigenspace cycle5.mulVecLin phiPlus) = 2 := by
  have := cycle5_spectrum.2 1
  simp only [cyc5Eigenvalues_one, cyc5Spaces_one] at this
  rw [this, finrank_cyc5Eig phiPlus_ne_zero]

theorem finrank_eigenspace_cycle5_phiMinus :
    finrank ℝ (Module.End.eigenspace cycle5.mulVecLin phiMinus) = 2 := by
  have := cycle5_spectrum.2 2
  simp only [cyc5Eigenvalues_two, cyc5Spaces_two] at this
  rw [this, finrank_cyc5Eig phiMinus_ne_zero]

end Brockian

/-
# Spectral tools

Reusable machinery for computing the *exact* spectrum (eigenvalues together with the
dimensions of the eigenspaces) of an operator built out of a fixed "base" operator and an
arithmetic "fibre" operator via a Kronecker (tensor) construction.

The three groups of results are:

* **Bookkeeping.** If a family of subspaces `S i` is contained in the eigenspaces of `T`
  for pairwise distinct eigenvalues, and if the dimensions of the `S i` already add up to
  the dimension of the whole space, then the `S i` *are* the eigenspaces and they span
  everything.  This turns an exact spectral computation into: exhibit enough eigenvectors,
  then count.

* **Kronecker intertwining.** `(A ⊗ₖ B) *ᵥ (f ⊛ g) = (A *ᵥ f) ⊛ (B *ᵥ g)` where `⊛` is the
  elementwise (Kronecker) product of vectors, plus the special cases needed for the
  all-ones matrix and the identity matrix.

* **Fibre powers.** The subspace `{F | ∀ i, F (i, ·) ∈ W}` of `l × n → K` and its dimension.
-/
import Mathlib

namespace Brockian

open Module Matrix
open scoped Kronecker

/-! ## Dimension bookkeeping for direct sums of eigenspaces -/

section Counting

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [Fintype ι] [DecidableEq ι]

/-- The dimension of an internal direct sum decomposition is the sum of the dimensions. -/
theorem finrank_eq_sum_of_isInternal (A : ι → Submodule K M) (h : DirectSum.IsInternal A) :
    finrank K M = ∑ i, finrank K (A i) := by
  have e : (DirectSum ι fun i => (A i : Submodule K M)) ≃ₗ[K] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h
  rw [← e.finrank_eq, Module.finrank_directSum]

/-- An independent family of subspaces whose dimensions add up to the dimension of the
ambient space spans the ambient space. -/
theorem iSup_eq_top_of_iSupIndep_of_finrank_sum (S : ι → Submodule K M) (hind : iSupIndep S)
    (hsum : ∑ i, finrank K (S i) = finrank K M) : ⨆ i, S i = ⊤ := by
  have hinj : Function.Injective (DirectSum.coeLinearMap S) := hind.dfinsupp_lsum_injective
  have hrank : finrank K (DirectSum ι fun i => (S i : Submodule K M)) = finrank K M := by
    rw [Module.finrank_directSum]; exact hsum
  have hsurj : Function.Surjective (DirectSum.coeLinearMap S) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  rw [← DirectSum.range_coeLinearMap, LinearMap.range_eq_top]
  exact hsurj

/-- **Master counting lemma.**  If `S i ≤ E i` for an independent family `E`, and the
dimensions of the `S i` add up to the dimension of the ambient space, then `S i = E i` for
every `i` and the family spans. -/
theorem eq_of_le_of_iSupIndep_of_finrank_sum (S E : ι → Submodule K M) (hle : ∀ i, S i ≤ E i)
    (hind : iSupIndep E) (hsum : ∑ i, finrank K (S i) = finrank K M) :
    (⨆ i, S i) = ⊤ ∧ ∀ i, E i = S i := by
  have hSind : iSupIndep S := hind.mono hle
  have htop : ⨆ i, S i = ⊤ := iSup_eq_top_of_iSupIndep_of_finrank_sum S hSind hsum
  refine ⟨htop, fun i => ?_⟩
  have hEtop : ⨆ i, E i = ⊤ := by rw [eq_top_iff, ← htop]; exact iSup_mono hle
  have hSint : DirectSum.IsInternal S :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top S).2 ⟨hSind, htop⟩
  have hEint : DirectSum.IsInternal E :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top E).2 ⟨hind, hEtop⟩
  have h1 := finrank_eq_sum_of_isInternal S hSint
  have h2 := finrank_eq_sum_of_isInternal E hEint
  have hle' : ∀ j ∈ Finset.univ, finrank K (S j) ≤ finrank K (E j) :=
    fun j _ => Submodule.finrank_mono (hle j)
  have := (Finset.sum_eq_sum_iff_of_le hle').1 (h1 ▸ h2) i (Finset.mem_univ i)
  exact (Submodule.eq_of_le_of_finrank_eq (hle i) this).symm

/-- **Exact spectrum from enough eigenvectors.**  Given pairwise distinct scalars `lam i`
and subspaces `S i` of the `lam i`-eigenspace of `T` whose dimensions add up to
`finrank K M`, the `lam i`-eigenspace is exactly `S i`, and the eigenspaces span. -/
theorem eigenspace_eq_of_finrank_sum (T : Module.End K M) (lam : ι → K)
    (hlam : Function.Injective lam) (S : ι → Submodule K M)
    (hle : ∀ i, S i ≤ T.eigenspace (lam i))
    (hsum : ∑ i, finrank K (S i) = finrank K M) :
    (⨆ i, T.eigenspace (lam i)) = ⊤ ∧ ∀ i, T.eigenspace (lam i) = S i := by
  have hind : iSupIndep fun i => T.eigenspace (lam i) := (T.eigenspaces_iSupIndep).comp hlam
  obtain ⟨htop, heq⟩ := eq_of_le_of_iSupIndep_of_finrank_sum S _ hle hind hsum
  refine ⟨?_, heq⟩
  rw [eq_top_iff, ← htop]
  exact iSup_mono hle

omit [FiniteDimensional K M] in
/-- If the eigenspaces attached to a family of scalars already span the whole space, then
there are no other eigenvalues. -/
theorem eigenvalue_mem_of_iSup_eq_top {ι' : Type*} (T : Module.End K M) (lam : ι' → K)
    (htop : (⨆ i, T.eigenspace (lam i)) = ⊤) {mu : K} (hmu : T.HasEigenvalue mu) :
    ∃ i, lam i = mu := by
  by_contra hcon
  push_neg at hcon
  have hdis := (T.eigenspaces_iSupIndep) mu
  have hle : (⨆ i, T.eigenspace (lam i)) ≤ ⨆ nu, ⨆ (_ : nu ≠ mu), T.eigenspace nu :=
    iSup_le fun i => le_iSup_of_le (lam i) (le_iSup_of_le (hcon i) le_rfl)
  rw [htop, top_le_iff] at hle
  rw [hle] at hdis
  exact hmu (by simpa using disjoint_top.1 hdis)

end Counting

/-! ## Kronecker products of vectors and the intertwining relation -/

/-- The Kronecker (elementwise tensor) product of two vectors. -/
def vkron {l n R : Type*} [Mul R] (f : l → R) (g : n → R) : l × n → R := fun p => f p.1 * g p.2

@[inherit_doc] infixl:100 " ⊛ " => vkron

@[simp] theorem vkron_apply {l n R : Type*} [Mul R] (f : l → R) (g : n → R) (p : l × n) :
    (f ⊛ g) p = f p.1 * g p.2 := rfl

/-- The all-ones matrix. -/
def allOnes (n : Type*) (R : Type*) [One R] : Matrix n n R := Matrix.of fun _ _ => 1

@[simp] theorem allOnes_apply {n R : Type*} [One R] (v w : n) : allOnes n R v w = 1 := rfl

section Kron

variable {l n R : Type*} [CommRing R] [Fintype l] [Fintype n]

/-- **Kronecker intertwining**: the Kronecker product of matrices acts on the Kronecker
product of vectors factorwise. -/
theorem kronecker_mulVec_vkron (A : Matrix l l R) (B : Matrix n n R) (f : l → R) (g : n → R) :
    (A ⊗ₖ B) *ᵥ (f ⊛ g) = (A *ᵥ f) ⊛ (B *ᵥ g) := by
  ext p
  obtain ⟨i, v⟩ := p
  simp only [vkron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => by ring

/-- The all-ones matrix maps a vector to the constant vector given by its total sum. -/
theorem allOnes_mulVec (g : n → R) : allOnes n R *ᵥ g = fun _ => ∑ v, g v := by
  ext v; simp [allOnes, Matrix.mulVec, dotProduct]

variable [DecidableEq l]

/-- The action of `A ⊗ₖ J + I ⊗ₖ B` on a Kronecker product of vectors: this is the basic
intertwining relation for a fixed base graph blown up by an arithmetic fibre. -/
theorem lex_mulVec_vkron (A : Matrix l l R) (B : Matrix n n R) (f : l → R) (g : n → R) :
    (A ⊗ₖ allOnes n R + (1 : Matrix l l R) ⊗ₖ B) *ᵥ (f ⊛ g)
      = (A *ᵥ f) ⊛ (fun _ => ∑ v, g v) + f ⊛ (B *ᵥ g) := by
  rw [Matrix.add_mulVec, kronecker_mulVec_vkron, kronecker_mulVec_vkron, allOnes_mulVec,
    Matrix.one_mulVec]

end Kron

/-! ## Fibre powers of a subspace -/

section FiberPow

variable {K : Type*} [Field K] {l n : Type*}

/-- The subspace of `l × n → K` consisting of those functions all of whose fibres
`F (i, ·)` lie in a given subspace `W` of `n → K`. -/
def fiberPow (l : Type*) (W : Submodule K (n → K)) : Submodule K (l × n → K) where
  carrier := {F | ∀ i, (fun v => F (i, v)) ∈ W}
  add_mem' hF hG := fun i => W.add_mem (hF i) (hG i)
  zero_mem' := fun _ => W.zero_mem
  smul_mem' c _ hF := fun i => W.smul_mem c (hF i)

@[simp] theorem mem_fiberPow {W : Submodule K (n → K)} {F : l × n → K} :
    F ∈ fiberPow l W ↔ ∀ i, (fun v => F (i, v)) ∈ W := Iff.rfl

/-- A fibre power is isomorphic to the `l`-fold power of the subspace. -/
def fiberPowEquiv (W : Submodule K (n → K)) : fiberPow l W ≃ₗ[K] (l → W) where
  toFun F i := ⟨fun v => F.1 (i, v), F.2 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun G := ⟨fun p => (G p.1).1 p.2, fun i => (G i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_fiberPow [Fintype l] (W : Submodule K (n → K)) [FiniteDimensional K W] :
    finrank K (fiberPow l W) = Fintype.card l * finrank K W := by
  rw [(fiberPowEquiv W).finrank_eq, Module.finrank_pi_fintype]
  simp

end FiberPow

/-! ## Normalized Laplacian of a regular graph -/

section NormLap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The normalized Laplacian `I - D⁻¹ A` of a `D`-regular graph with adjacency matrix `A`. -/
noncomputable def normLap (D : ℝ) (A : Matrix n n ℝ) : Matrix n n ℝ := 1 - D⁻¹ • A

/-- Eigenvectors of the adjacency matrix for `lam` are exactly the eigenvectors of the
normalized Laplacian for `1 - lam / D`. -/
theorem eigenspace_normLap (D : ℝ) (hD : D ≠ 0) (A : Matrix n n ℝ) (lam : ℝ) :
    Module.End.eigenspace (normLap D A).mulVecLin (1 - lam / D)
      = Module.End.eigenspace A.mulVecLin lam := by
  ext x
  simp only [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, normLap, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul, one_smul, sub_right_inj]
  constructor
  · intro h
    have h2 := congrArg (fun y => D • y) h
    simp only [smul_smul, mul_inv_cancel₀ hD, one_smul] at h2
    rw [h2]
    congr 1
    field_simp
  · intro h
    rw [h, smul_smul]
    congr 1
    field_simp

end NormLap

end Brockian

