import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]

theorem jointlyDiagonalizable_of_commute (ρ : X → Matrix n n ℂ)
    (hherm : ∀ x, (ρ x).IsHermitian) (hcomm : ∀ x x', Commute (ρ x) (ρ x')) :
    JointlyDiagonalizable ρ := by
  classical
  -- pass to linear maps on Euclidean space
  set T : X → Module.End ℂ (EuclideanSpace ℂ n) := fun x => Matrix.toEuclideanLin (ρ x) with hTdef
  have hmul : ∀ (C D : Matrix n n ℂ), Matrix.toEuclideanLin C * Matrix.toEuclideanLin D
      = Matrix.toEuclideanLin (C * D) := by
    intro C D
    ext v i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hT : ∀ x, (T x).IsSymmetric := fun x => Matrix.isHermitian_iff_isSymmetric.1 (hherm x)
  have hC : Pairwise (Commute on T) := by
    intro x x' _
    show T x * T x' = T x' * T x
    rw [hTdef]; simp only
    rw [hmul, hmul, (hcomm x x').eq]
  -- the joint eigenspaces decompose the space
  have hint := LinearMap.IsSymmetric.LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    hT hC
  set V : (X → ℂ) → Submodule ℂ (EuclideanSpace ℂ n) :=
    fun α => ⨅ x, (T x).eigenspace (α x) with hV
  have hOF := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  set bas := hint.collectedBasis (fun α => (stdOrthonormalBasis ℂ (V α)).toBasis) with hbas
  haveI : Fintype ((α : X → ℂ) × Fin (Module.finrank ℂ (V α))) :=
    FiniteDimensional.fintypeBasisIndex bas
  have horth : Orthonormal ℂ bas := by
    simpa [hbas] using hOF.orthonormal_sigma_orthonormal
      (show ∀ α, Orthonormal ℂ (stdOrthonormalBasis ℂ (V α)).toBasis by simp)
  set ob := bas.toOrthonormalBasis horth with hob
  have hobcoe : ⇑ob = ⇑bas := Module.Basis.coe_toOrthonormalBasis _ _
  have hmem : ∀ a, ob a ∈ V a.1 := by
    intro a
    rw [hobcoe]
    exact hint.collectedBasis_mem (fun α => (stdOrthonormalBasis ℂ (V α)).toBasis) a
  -- reindex the basis by `n`
  have hcard : Fintype.card ((α : X → ℂ) × Fin (Module.finrank ℂ (V α))) = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis bas
    have h2 : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
    omega
  set e := Fintype.equivOfCardEq hcard with he
  set b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := ob.reindex e with hbdef
  have hbmem : ∀ i : n, b i ∈ V (e.symm i).1 := by
    intro i
    rw [hbdef, OrthonormalBasis.reindex_apply]
    exact hmem _
  -- the eigenvalues are real
  have heig : ∀ (i : n) (x : X), T x (b i) = ((e.symm i).1 x) • b i := by
    intro i x
    have h : b i ∈ ⨅ x, (T x).eigenspace ((e.symm i).1 x) := hbmem i
    rw [Submodule.mem_iInf] at h
    exact (Module.End.mem_eigenspace_iff).1 (h x)
  have hbne : ∀ i : n, b i ≠ 0 := by
    intro i h
    have := b.orthonormal.1 i
    rw [h] at this
    simp at this
  have hreal : ∀ (i : n) (x : X), (((e.symm i).1 x).re : ℂ) = (e.symm i).1 x := by
    intro i x
    have hev : Module.End.HasEigenvalue (T x) ((e.symm i).1 x) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨(Module.End.mem_eigenspace_iff).2 (heig i x),
        hbne i⟩
    have := (hT x).conj_eigenvalue_eq_self hev
    exact Complex.conj_eq_iff_re.1 this
  set v : X → n → ℝ := fun x i => ((e.symm i).1 x).re with hvdef
  -- the unitary whose columns are the joint eigenvectors
  set U : Matrix n n ℂ := (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix ⇑b with hUdef
  have hUmem : U ∈ Matrix.unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hUapply : ∀ i j : n, U i j = (b j) i := fun _ _ => rfl
  have hUcol : ∀ j : n, U *ᵥ Pi.single j 1 = ⇑(b j) := by
    intro j
    rw [Matrix.mulVec_single_one]
    rfl
  -- the eigenvector equation in matrix form
  have hmulVec : ∀ (x : X) (j : n), ρ x *ᵥ ⇑(b j) = (v x j : ℂ) • ⇑(b j) := by
    intro x j
    have h := heig j x
    rw [hTdef] at h
    simp only [Matrix.toLpLin_apply] at h
    have h2 := congrArg (fun w : EuclideanSpace ℂ n => WithLp.ofLp w) h
    simpa [hvdef, hreal j x] using h2
  refine ⟨U, hUmem, fun x => ⟨v x, ?_⟩⟩
  have hUU : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).1 hUmem
    simpa using this
  have hkey : ρ x * U = U * Matrix.diagonal (fun i => (v x i : ℂ)) := by
    ext i j
    have hL : (ρ x * U) *ᵥ Pi.single j 1 = (v x j : ℂ) • ⇑(b j) := by
      rw [← Matrix.mulVec_mulVec, hUcol j, hmulVec x j]
    have hR : (U * Matrix.diagonal (fun i => (v x i : ℂ))) *ᵥ Pi.single j 1
        = (v x j : ℂ) • ⇑(b j) := by
      rw [← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single, mul_one]
      have hs : (Pi.single j ((v x j : ℂ)) : n → ℂ)
          = (v x j : ℂ) • (Pi.single j 1 : n → ℂ) := by
        ext k
        by_cases hk : k = j <;> simp [Pi.single_apply, hk]
      rw [hs, mulVec_smul, hUcol j]
    have := hL.trans hR.symm
    have hcol := congrFun this i
    simpa [Matrix.mulVec_single_one] using hcol
  calc ρ x = ρ x * (U * Uᴴ) := by rw [hUU, mul_one]
    _ = (ρ x * U) * Uᴴ := by rw [mul_assoc]
    _ = U * Matrix.diagonal (fun i => (v x i : ℂ)) * Uᴴ := by rw [hkey]

/-! ### The Holevo bound for commuting ensembles -/

variable {Y : Type*} [Fintype X] [Fintype Y]

/-- The mutual information obtained from any POVM measurement on an ensemble of pairwise
commuting states is at most the Holevo χ quantity of the ensemble. -/
theorem measInfo_le_holevoChi {p : X → ℝ} {ρ : X → Matrix n n ℂ} {E : Y → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hE : IsPOVM E) (hcomm : ∀ x x', Commute (ρ x) (ρ x')) :
    measInfo p ρ E ≤ holevoChi p ρ :=
  measInfo_le_holevoChi_of_jointlyDiagonalizable hens hE
    (jointlyDiagonalizable_of_commute ρ (fun x => (hens.state x).psd.1) hcomm)

/-- **Holevo bound**: the accessible information of an ensemble of pairwise commuting states is
at most its Holevo χ quantity. -/
theorem holevo_bound {p : X → ℝ} {ρ : X → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hcomm : ∀ x x', Commute (ρ x) (ρ x')) :
    accessibleInfo p ρ ≤ holevoChi p ρ :=
  holevo_bound_of_jointlyDiagonalizable hens
    (jointlyDiagonalizable_of_commute ρ (fun x => (hens.state x).psd.1) hcomm)

end QI

import Mathlib
import RequestProject.ClassicalInfo

/-!
# The Holevo bound

Finite-dimensional quantum states are modelled as positive semidefinite complex matrices of
unit trace, measurements as POVMs, and the von Neumann entropy through the eigenvalues of the
density matrix.

The main results are:

* `QI.measInfo_le_holevoChi_of_jointlyDiagonalizable` : the mutual information between the
  classical label of an ensemble and the outcome of *any* POVM measurement performed on it is at
  most the Holevo χ quantity of the ensemble;
* `QI.holevo_bound_of_jointlyDiagonalizable` : the accessible information of an ensemble (the
  supremum of the above over all POVMs) is at most its Holevo χ quantity.

The versions phrased for commuting ensembles, `QI.measInfo_le_holevoChi` and `QI.holevo_bound`,
are in `RequestProject.SimulDiag`.

**Scope.** Both results are proved here for ensembles whose states share a common orthonormal
eigenbasis (`QI.JointlyDiagonalizable`), equivalently for ensembles of pairwise commuting states;
the measurement is an arbitrary POVM. The proof reduces the bound, via the joint spectral
decomposition, to the classical data-processing inequality `QI.classical_holevo`.
The general (noncommuting) case of Holevo's theorem rests on the monotonicity of the quantum
relative entropy under measurements, which is not available in Mathlib and is not developed here.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {n X Y : Type*} [Fintype n] [DecidableEq n] [Fintype X] [Fintype Y]

/-! ### Basic definitions -/

/-- A finite-dimensional quantum state (density matrix). -/
structure IsState (ρ : Matrix n n ℂ) : Prop where
  psd : ρ.PosSemidef
  trace_one : ρ.trace = 1

/-- A POVM with outcomes in `Y`. -/
structure IsPOVM (E : Y → Matrix n n ℂ) : Prop where
  psd : ∀ y, (E y).PosSemidef
  sum_eq_one : ∑ y, E y = 1

/-- An ensemble: a probability distribution `p` on `X` together with states `ρ x`. -/
structure IsEnsemble (p : X → ℝ) (ρ : X → Matrix n n ℂ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x, p x = 1
  state : ∀ x, IsState (ρ x)

/-- The von Neumann entropy (in nats) of a density matrix, defined as the Shannon entropy of its
spectrum. -/
noncomputable def vnEntropy (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

/-- The average state of an ensemble. -/
noncomputable def avgState (p : X → ℝ) (ρ : X → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ x, (p x : ℂ) • ρ x

/-- The probability of the outcome corresponding to the POVM element `E` in the state `ρ`. -/
noncomputable def outcomeProb (ρ E : Matrix n n ℂ) : ℝ := (ρ * E).trace.re

/-- The Holevo χ quantity of an ensemble. -/
noncomputable def holevoChi (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  vnEntropy (avgState p ρ) - ∑ x, p x * vnEntropy (ρ x)

/-- The mutual information between the classical label `X` and the outcome of the measurement
`E` performed on the ensemble. -/
noncomputable def measInfo (p : X → ℝ) (ρ : X → Matrix n n ℂ) (E : Y → Matrix n n ℂ) : ℝ :=
  shannonEntropy (fun y => ∑ x, p x * outcomeProb (ρ x) (E y))
    - ∑ x, p x * shannonEntropy (fun y => outcomeProb (ρ x) (E y))

/-- The accessible information of an ensemble: the supremum of the mutual information over all
POVMs (with an arbitrary finite number of outcomes). -/
noncomputable def accessibleInfo (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  sSup {I : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ), IsPOVM E ∧ I = measInfo p ρ E}

/-- An ensemble is *jointly diagonalizable* when all its states are diagonal in one common
orthonormal basis; equivalently (for Hermitian matrices), when they commute pairwise. -/
def JointlyDiagonalizable (ρ : X → Matrix n n ℂ) : Prop :=
  ∃ U : Matrix n n ℂ, U ∈ Matrix.unitaryGroup n ℂ ∧
    ∀ x, ∃ v : n → ℝ, ρ x = U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ

omit [Fintype X] in
/-- A jointly diagonalizable family of states is a commuting family. For the converse, see
`QI.jointlyDiagonalizable_of_commute`. -/
lemma JointlyDiagonalizable.commute {ρ : X → Matrix n n ℂ} (h : JointlyDiagonalizable ρ)
    (x x' : X) : Commute (ρ x) (ρ x') := by
  obtain ⟨U, hU, hv⟩ := h
  obtain ⟨v, hvx⟩ := hv x
  obtain ⟨w, hwx⟩ := hv x'
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  have hdd : Matrix.diagonal (fun i => (v i : ℂ)) * Matrix.diagonal (fun i => (w i : ℂ))
      = Matrix.diagonal (fun i => (w i : ℂ)) * Matrix.diagonal (fun i => (v i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_diagonal_iff.2 fun i => by ring
  show ρ x * ρ x' = ρ x' * ρ x
  rw [hvx, hwx]
  calc U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ *
        (U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ)
      = U * (Matrix.diagonal (fun i => (v i : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun i => (w i : ℂ))) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal (fun i => (w i : ℂ)) * (Uᴴ * U) *
          Matrix.diagonal (fun i => (v i : ℂ))) * Uᴴ := by
        rw [hUU, mul_one, mul_one, hdd]
    _ = U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ *
          (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ) := by
        simp only [Matrix.mul_assoc]

/-! ### A sanity check: perfectly distinguishable states -/

/-- Measuring the ensemble `{(1/2, |0⟩⟨0|), (1/2, |1⟩⟨1|)}` in the computational basis yields
one nat (`log 2`) of information; in particular the definitions above are not degenerate. -/
example :
    measInfo (n := Fin 2) (X := Fin 2) (Y := Fin 2) (fun _ => 1 / 2)
      (fun x => Matrix.diagonal (fun i => if i = x then (1 : ℂ) else 0))
      (fun y => Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0)) = Real.log 2 := by
  have hprob : ∀ x y : Fin 2,
      outcomeProb (Matrix.diagonal (fun i => if i = x then (1 : ℂ) else 0))
        (Matrix.diagonal (fun i => if i = y then (1 : ℂ) else 0)) = if x = y then 1 else 0 := by
    intro x y
    rw [outcomeProb, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    by_cases h : x = y <;> simp [h, Fin.sum_univ_two, Fin.ext_iff] <;>
      fin_cases x <;> fin_cases y <;> simp_all
  rw [measInfo]
  simp only [hprob]
  rw [shannonEntropy]
  have h1 : ∀ y : Fin 2, (∑ x : Fin 2, (1 / 2 : ℝ) * (if x = y then 1 else 0)) = 1 / 2 := by
    intro y; fin_cases y <;> simp
  simp only [h1]
  have h2 : ∀ x : Fin 2, shannonEntropy (fun y : Fin 2 => if x = y then (1 : ℝ) else 0) = 0 := by
    intro x
    rw [shannonEntropy]
    fin_cases x <;> simp [Fin.sum_univ_two]
  simp only [h2]
  simp [Real.negMulLog, Real.log_inv]

/-! ### Elementary matrix facts -/

lemma psd_diag_nonneg {M : Matrix n n ℂ} (h : M.PosSemidef) (i : n) : 0 ≤ (M i i).re := by
  have := h.re_dotProduct_nonneg (Pi.single i 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using this

lemma trace_diagonal_mul (d : n → ℂ) (M : Matrix n n ℂ) :
    (Matrix.diagonal d * M).trace = ∑ i, d i * M i i := by
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-- The eigenvalues of `U * diagonal v * Uᴴ` are the entries of `v`, up to a permutation; hence
any sum `∑ f (eigenvalue)` can be computed from `v`. -/
lemma sum_eigenvalues_conj_diagonal {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (v : n → ℝ) (f : ℝ → ℝ)
    (hH : (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).IsHermitian) :
    ∑ i, f (hH.eigenvalues i) = ∑ i, f (v i) := by
  classical
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  -- the characteristic polynomial is that of the diagonal matrix
  have hchar : (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C ((v i : ℂ))) := by
    rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, hUU, mul_one, Matrix.charpoly_diagonal]
  have hroots : (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).charpoly.roots
      = Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val := by
    rw [hchar, Finset.prod_eq_multiset_prod,
      show (Multiset.map (fun i => Polynomial.X - Polynomial.C ((v i : ℂ))) Finset.univ.val)
        = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hmul : Multiset.map (RCLike.ofReal ∘ hH.eigenvalues) (Finset.univ (α := n)).val
      = Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val := by
    rw [← hH.roots_charpoly_eq_eigenvalues, hroots]
  have := congrArg (Multiset.map (fun z : ℂ => f z.re)) hmul
  rw [Multiset.map_map, Multiset.map_map] at this
  simpa [Function.comp] using congrArg Multiset.sum this

lemma isHermitian_conj_diagonal (U : Matrix n n ℂ) (v : n → ℝ) :
    (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).IsHermitian := by
  have hD : (Matrix.diagonal (fun i => (v i : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.2
    intro i
    show star ((v i : ℂ)) = _
    exact Complex.conj_ofReal _
  have := Matrix.isHermitian_conjTranspose_mul_mul (A := Matrix.diagonal (fun i => (v i : ℂ)))
    Uᴴ hD
  simpa using this

lemma vnEntropy_conj_diagonal {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (v : n → ℝ) :
    vnEntropy (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ) = shannonEntropy v := by
  rw [vnEntropy, dif_pos (isHermitian_conj_diagonal U v), shannonEntropy]
  exact sum_eigenvalues_conj_diagonal hU v Real.negMulLog _

/-! ### The Holevo bound for jointly diagonalizable ensembles -/

/-- The mutual information obtained from any POVM measurement on a jointly diagonalizable
ensemble is at most the Holevo χ quantity of the ensemble. -/
theorem measInfo_le_holevoChi_of_jointlyDiagonalizable {p : X → ℝ} {ρ : X → Matrix n n ℂ} {E : Y → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hE : IsPOVM E) (hdiag : JointlyDiagonalizable ρ) :
    measInfo p ρ E ≤ holevoChi p ρ := by
  classical
  obtain ⟨U, hU, hv⟩ := hdiag
  choose v hv using hv
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  set A : Y → n → ℝ := fun y i => ((Uᴴ * E y * U) i i).re with hAdef
  -- the induced classical channel is stochastic
  have hAnn : ∀ y i, 0 ≤ A y i := fun y i =>
    psd_diag_nonneg ((hE.psd y).conjTranspose_mul_mul_same U) i
  have hAcol : ∀ i, ∑ y, A y i = 1 := by
    intro i
    have hsum : ∑ y, Uᴴ * E y * U = (1 : Matrix n n ℂ) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hE.sum_eq_one, mul_one, hUU]
    have : ∑ y, A y i = ((∑ y, Uᴴ * E y * U) i i).re := by
      rw [Matrix.sum_apply, hAdef]
      simp
    rw [this, hsum]
    simp
  -- the spectra are nonnegative
  have hD : ∀ x, Uᴴ * ρ x * U = Matrix.diagonal (fun i => (v x i : ℂ)) := by
    intro x
    rw [hv x]
    calc Uᴴ * (U * Matrix.diagonal (fun i => (v x i : ℂ)) * Uᴴ) * U
        = (Uᴴ * U) * Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun i => (v x i : ℂ)) := by rw [hUU, one_mul, mul_one]
  have hvnn : ∀ x i, 0 ≤ v x i := by
    intro x i
    have h := psd_diag_nonneg ((hens.state x).psd.conjTranspose_mul_mul_same U) i
    rw [hD x] at h
    simpa using h
  -- entropies of the individual states
  have hent : ∀ x, vnEntropy (ρ x) = shannonEntropy (v x) := by
    intro x
    rw [hv x]
    exact vnEntropy_conj_diagonal hU (v x)
  -- the average state
  have havg : avgState p ρ
      = U * Matrix.diagonal (fun i => ((∑ x, p x * v x i : ℝ) : ℂ)) * Uᴴ := by
    rw [avgState]
    have h1 : ∀ x, (p x : ℂ) • ρ x
        = U * ((p x : ℂ) • Matrix.diagonal (fun i => (v x i : ℂ))) * Uᴴ := by
      intro x
      rw [hv x, Matrix.mul_smul, Matrix.smul_mul]
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    congr 1
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_sum, Complex.ofReal_mul]
    · simp [Matrix.sum_apply, h]
  -- outcome probabilities
  have hprob : ∀ x y, outcomeProb (ρ x) (E y) = ∑ i, A y i * v x i := by
    intro x y
    rw [outcomeProb, hv x]
    have h1 : U * Matrix.diagonal (fun i => (v x i : ℂ)) * Uᴴ * E y
        = U * (Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * E y)) := by
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    have h2 : Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * E y) * U
        = Matrix.diagonal (fun i => (v x i : ℂ)) * (Uᴴ * E y * U) := by
      simp only [Matrix.mul_assoc]
    rw [h2, trace_diagonal_mul]
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.re_ofReal_mul]
      ring
  -- reduce to the classical statement
  rw [measInfo, holevoChi, havg, vnEntropy_conj_diagonal hU]
  simp only [hprob, hent]
  exact classical_holevo p v A hens.nonneg hvnn hAnn hAcol

/-- **Holevo bound**: the accessible information of a jointly diagonalizable ensemble is at most
its Holevo χ quantity. -/
theorem holevo_bound_of_jointlyDiagonalizable {p : X → ℝ} {ρ : X → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hdiag : JointlyDiagonalizable ρ) :
    accessibleInfo p ρ ≤ holevoChi p ρ := by
  refine csSup_le ?_ ?_
  · refine ⟨measInfo p ρ (fun _ : Fin 1 => (1 : Matrix n n ℂ)), 1,
      (fun _ : Fin 1 => (1 : Matrix n n ℂ)), ⟨fun _ => Matrix.PosSemidef.one, by simp⟩, rfl⟩
  · rintro b ⟨m, E, hE, rfl⟩
    exact measInfo_le_holevoChi_of_jointlyDiagonalizable hens hE hdiag

end QI

import Mathlib

/-!
# Classical information-theoretic core

This file develops the elementary classical facts that underlie the Holevo bound:

* `QI.shannonEntropy` : Shannon entropy of a finite probability vector;
* `QI.relEntropy` : the Kullback-Leibler divergence of two finite nonnegative vectors;
* `QI.log_sum_ineq` : the log-sum inequality;
* `QI.relEntropy_channel_le` : the data-processing inequality for the KL divergence
  under a classical (column-stochastic) channel;
* `QI.mutualInfo_eq_sum_relEntropy` : mutual information as an average divergence;
* `QI.classical_holevo` : the classical Holevo/data-processing bound.

All entropies use natural logarithms (nats).
-/

open scoped BigOperators

namespace QI

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

/-- Shannon entropy of a finite (probability) vector, in nats. -/
noncomputable def shannonEntropy (P : Y → ℝ) : ℝ := ∑ y, Real.negMulLog (P y)

/-- Kullback-Leibler divergence of two finite nonnegative vectors, using the convention
`Real.log 0 = 0`. -/
noncomputable def relEntropy (a b : Y → ℝ) : ℝ :=
  ∑ y, (a y * Real.log (a y) - a y * Real.log (b y))

lemma relEntropy_eq_sum (a b : Y → ℝ) :
    relEntropy a b = ∑ y, (a y * Real.log (a y) - a y * Real.log (b y)) := rfl

/-- The basic inequality `log x ≥ 1 - 1/x` for `x > 0`, in the form used below. -/
lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.add_one_le_exp (Real.log x⁻¹)
  rw [Real.exp_log (by positivity), Real.log_inv] at h
  linarith

/-- **Log-sum inequality**. -/
lemma log_sum_ineq (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log (∑ i, a i) - (∑ i, a i) * Real.log (∑ i, b i) ≤ relEntropy a b := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  rcases eq_or_lt_of_le hA0 with hA_eq | hApos
  · -- all `a i = 0`
    have hzero : ∀ i, a i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).1 hA_eq.symm i (Finset.mem_univ i)
      exact this
    have hA' : A = 0 := hA_eq.symm
    simp [relEntropy, hzero, hA']
  · have hBpos : 0 < B := by
      rcases eq_or_lt_of_le hB0 with hB_eq | h
      · exfalso
        have hzero : ∀ i, b i = 0 := by
          intro i
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).1 hB_eq.symm i
            (Finset.mem_univ i)
        have : A = 0 := by
          rw [hA]; exact Finset.sum_eq_zero fun i _ => hab i (hzero i)
        exact absurd this (ne_of_gt hApos)
      · exact h
    -- Pointwise bound on the summands.
    have key : ∀ i ∈ Finset.univ,
        a i - (A / B) * b i ≤ (a i * Real.log (a i) - a i * Real.log (b i))
          - (a i * Real.log A - a i * Real.log B) := by
      intro i _
      rcases eq_or_lt_of_le (ha i) with hai | hai
      · -- a i = 0
        have hai' : a i = 0 := hai.symm
        have hnn : 0 ≤ (A / B) * b i := mul_nonneg (div_nonneg hA0 hB0) (hb i)
        calc a i - (A / B) * b i ≤ 0 := by rw [hai']; linarith
          _ = (a i * Real.log (a i) - a i * Real.log (b i))
                - (a i * Real.log A - a i * Real.log B) := by simp [hai']
      · have hbi : 0 < b i := by
          rcases eq_or_lt_of_le (hb i) with h | h
          · exact absurd (hab i h.symm) (ne_of_gt hai)
          · exact h
        -- bracket = log ((a i * B) / (b i * A))
        have hx : 0 < (a i * B) / (b i * A) :=
          div_pos (mul_pos hai hBpos) (mul_pos hbi hApos)
        have hlog : Real.log ((a i * B) / (b i * A))
            = Real.log (a i) - Real.log (b i) - Real.log A + Real.log B := by
          rw [Real.log_div (ne_of_gt (mul_pos hai hBpos)) (ne_of_gt (mul_pos hbi hApos)),
            Real.log_mul (ne_of_gt hai) (ne_of_gt hBpos),
            Real.log_mul (ne_of_gt hbi) (ne_of_gt hApos)]
          ring
        have hineq := one_sub_inv_le_log hx
        rw [hlog] at hineq
        have hmul := mul_le_mul_of_nonneg_left hineq (le_of_lt hai)
        have hai0 : a i ≠ 0 := ne_of_gt hai
        have hbi0 : b i ≠ 0 := ne_of_gt hbi
        have hA0' : A ≠ 0 := ne_of_gt hApos
        have hB0' : B ≠ 0 := ne_of_gt hBpos
        have hinv : (a i) * ((a i * B) / (b i * A))⁻¹ = (A / B) * b i := by
          rw [inv_div]
          field_simp
        calc a i - (A / B) * b i
            = a i * (1 - ((a i * B) / (b i * A))⁻¹) := by rw [mul_sub, mul_one, hinv]
          _ ≤ a i * (Real.log (a i) - Real.log (b i) - Real.log A + Real.log B) := hmul
          _ = (a i * Real.log (a i) - a i * Real.log (b i))
                - (a i * Real.log A - a i * Real.log B) := by ring
    have hsum := Finset.sum_le_sum key
    have hleft : ∑ i, (a i - (A / B) * b i) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hA, ← hB]
      field_simp
      ring
    have hright : ∑ i, ((a i * Real.log (a i) - a i * Real.log (b i))
          - (a i * Real.log A - a i * Real.log B))
        = relEntropy a b - (A * Real.log A - A * Real.log B) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← hA]
    rw [hleft, hright] at hsum
    linarith

/-- Data-processing inequality for the KL divergence under a column-stochastic channel
`A : Y → I → ℝ`. -/
lemma relEntropy_channel_le (lam mu : I → ℝ) (A : Y → I → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ i, 0 ≤ mu i) (habs : ∀ i, mu i = 0 → lam i = 0)
    (hA : ∀ y i, 0 ≤ A y i) (hAcol : ∀ i, ∑ y, A y i = 1) :
    relEntropy (fun y => ∑ i, A y i * lam i) (fun y => ∑ i, A y i * mu i) ≤ relEntropy lam mu := by
  have step : ∀ y ∈ (Finset.univ : Finset Y),
      ((∑ i, A y i * lam i) * Real.log (∑ i, A y i * lam i)
        - (∑ i, A y i * lam i) * Real.log (∑ i, A y i * mu i))
      ≤ ∑ i, A y i * (lam i * Real.log (lam i) - lam i * Real.log (mu i)) := by
    intro y _
    have h := log_sum_ineq (fun i => A y i * lam i) (fun i => A y i * mu i)
      (fun i => mul_nonneg (hA y i) (hlam i)) (fun i => mul_nonneg (hA y i) (hmu i))
      (by
        intro i hi
        rcases mul_eq_zero.1 hi with h | h
        · simp [h]
        · simp [habs i h])
    refine h.trans_eq ?_
    rw [relEntropy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_lt_of_le (hA y i) with hAi | hAi
    · simp [← hAi]
    · rcases eq_or_lt_of_le (hlam i) with hl | hl
      · simp [← hl]
      · have hmi : 0 < mu i := by
          rcases eq_or_lt_of_le (hmu i) with h' | h'
          · exact absurd (habs i h'.symm) (ne_of_gt hl)
          · exact h'
        rw [Real.log_mul (ne_of_gt hAi) (ne_of_gt hl), Real.log_mul (ne_of_gt hAi) (ne_of_gt hmi)]
        ring
  have hsum := Finset.sum_le_sum step
  refine hsum.trans_eq ?_
  rw [Finset.sum_comm]
  rw [relEntropy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, hAcol i, one_mul]

lemma shannonEntropy_eq_neg_sum (P : Y → ℝ) :
    shannonEntropy P = -∑ y, P y * Real.log (P y) := by
  rw [shannonEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by simp [Real.negMulLog]

/-- Mutual information (as `H(P̄) - ∑ₓ pₓ H(Pₓ)`) equals the average divergence from the
mean distribution. -/
lemma mutualInfo_eq_sum_relEntropy (p : X → ℝ) (Q : X → Y → ℝ) :
    ∑ x, p x * relEntropy (Q x) (fun y => ∑ x', p x' * Q x' y)
      = shannonEntropy (fun y => ∑ x, p x * Q x y) - ∑ x, p x * shannonEntropy (Q x) := by
  set Qbar : Y → ℝ := fun y => ∑ x, p x * Q x y with hQbar
  have e1 : ∀ x, relEntropy (Q x) Qbar
      = (-shannonEntropy (Q x)) - ∑ y, Q x y * Real.log (Qbar y) := by
    intro x
    rw [relEntropy, Finset.sum_sub_distrib, shannonEntropy_eq_neg_sum, neg_neg]
  have e2 : ∑ x, p x * (∑ y, Q x y * Real.log (Qbar y)) = -shannonEntropy Qbar := by
    rw [shannonEntropy_eq_neg_sum, neg_neg]
    have : ∀ x, p x * (∑ y, Q x y * Real.log (Qbar y))
        = ∑ y, p x * Q x y * Real.log (Qbar y) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul]
  calc ∑ x, p x * relEntropy (Q x) Qbar
      = ∑ x, (p x * (-shannonEntropy (Q x)) - p x * ∑ y, Q x y * Real.log (Qbar y)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [e1 x, mul_sub]
    _ = (∑ x, p x * (-shannonEntropy (Q x)))
          - ∑ x, p x * ∑ y, Q x y * Real.log (Qbar y) := Finset.sum_sub_distrib _ _
    _ = shannonEntropy Qbar - ∑ x, p x * shannonEntropy (Q x) := by
        rw [e2]
        simp [Finset.sum_neg_distrib]
        ring

/-- **Classical Holevo / data-processing bound**: processing the letter alphabet `I` through a
stochastic channel `A` cannot increase the mutual information with `X`. -/
theorem classical_holevo (p : X → ℝ) (lam : X → I → ℝ) (A : Y → I → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hlam : ∀ x i, 0 ≤ lam x i)
    (hA : ∀ y i, 0 ≤ A y i) (hAcol : ∀ i, ∑ y, A y i = 1) :
    shannonEntropy (fun y => ∑ x, p x * (∑ i, A y i * lam x i))
        - ∑ x, p x * shannonEntropy (fun y => ∑ i, A y i * lam x i)
      ≤ shannonEntropy (fun i => ∑ x, p x * lam x i) - ∑ x, p x * shannonEntropy (lam x) := by
  rw [← mutualInfo_eq_sum_relEntropy, ← mutualInfo_eq_sum_relEntropy]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases eq_or_lt_of_le (hp x) with hpx | hpx
  · simp [← hpx]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpx)
  have habs : ∀ i, (∑ x', p x' * lam x' i) = 0 → lam x i = 0 := by
    intro i hi
    have hnn : ∀ x' ∈ (Finset.univ : Finset X), 0 ≤ p x' * lam x' i :=
      fun x' _ => mul_nonneg (hp x') (hlam x' i)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hi x (Finset.mem_univ x)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt hpx)
    · exact h
  have key := relEntropy_channel_le (lam x) (fun i => ∑ x', p x' * lam x' i) A
    (hlam x) (fun i => Finset.sum_nonneg fun x' _ => mul_nonneg (hp x') (hlam x' i))
    habs hA hAcol
  have hfun : (fun y => ∑ x', p x' * ∑ i, A y i * lam x' i)
      = fun y => ∑ i, A y i * ∑ x', p x' * lam x' i := by
    funext y
    have h1 : ∀ x', p x' * (∑ i, A y i * lam x' i) = ∑ i, p x' * (A y i * lam x' i) :=
      fun x' => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl fun x' _ => h1 x', Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring
  rw [hfun]
  exact key

end QI

import Mathlib
import RequestProject.ClassicalInfo
import RequestProject.Holevo
import RequestProject.SimulDiag

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

