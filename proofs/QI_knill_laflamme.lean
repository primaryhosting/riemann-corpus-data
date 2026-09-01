import Mathlib
/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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

namespace QI

open Matrix Finset

variable {N : Type} [Fintype N] [DecidableEq N] {n : ℕ}

/-- `P` is the orthogonal projector onto a code subspace: it is Hermitian and idempotent. -/
structure IsCodeProjector (P : Matrix N N ℂ) : Prop where
  herm : P.IsHermitian
  idem : P * P = P

/-- The **Knill–Laflamme conditions** for a code with projector `P` and a finite family of
error operators `E`: there is a (necessarily Hermitian, positive semidefinite) matrix `α`
with `P Eᵢ† Eⱼ P = αᵢⱼ P` for all `i, j`. -/
def KnillLaflammeConditions (P : Matrix N N ℂ) (E : Fin n → Matrix N N ℂ) : Prop :=
  ∃ α : Matrix (Fin n) (Fin n) ℂ, ∀ i j, P * (E i)ᴴ * E j * P = α i j • P

/-- The code with projector `P` **corrects** the error set `E`: there is a recovery operation,
given by a finite family of Kraus operators `R` with `∑ₖ Rₖ† Rₖ = 1`, which maps every erroneous
version `Eᵢ` of a code state back to a multiple of the state itself, i.e.
`Rₖ Eᵢ P = c k i • P`. -/
def Corrects (P : Matrix N N ℂ) (E : Fin n → Matrix N N ℂ) : Prop :=
  ∃ (m : ℕ) (R : Fin m → Matrix N N ℂ) (c : Fin m → Fin n → ℂ),
    (∑ k, (R k)ᴴ * R k = 1) ∧ ∀ k i, R k * E i * P = c k i • P

/-! ### Auxiliary lemmas -/

omit [Fintype N] [DecidableEq N] in
private lemma smul_cancel_of_ne_zero {P : Matrix N N ℂ} (hP : P ≠ 0) {a b : ℂ}
    (h : a • P = b • P) : a = b := by
  have h' : (a - b) • P = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h' with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hP

omit [DecidableEq N] in
private lemma diag_conjTranspose_mul_self (A : Matrix N N ℂ) (i : N) :
    (Aᴴ * A) i i = ((∑ j, Complex.normSq (A j i) : ℝ) : ℂ) := by
  simp [Matrix.mul_apply, Complex.normSq_eq_conj_mul_self]

omit [DecidableEq N] in
private lemma eq_zero_of_conjTranspose_mul_self {A : Matrix N N ℂ} (h : Aᴴ * A = 0) : A = 0 := by
  ext j i
  have h1 : ((∑ k, Complex.normSq (A k i) : ℝ) : ℂ) = 0 := by
    rw [← diag_conjTranspose_mul_self A i, h]; simp
  have h2 : (∑ k, Complex.normSq (A k i)) = 0 := by exact_mod_cast h1
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg (A k i))).mp h2 j (Finset.mem_univ j)
  simpa using h3

omit [DecidableEq N] in
private lemma proj_diag {P : Matrix N N ℂ} (hP : IsCodeProjector P) (i : N) :
    P i i = ((∑ j, Complex.normSq (P j i) : ℝ) : ℂ) := by
  have hPP : Pᴴ * P = P := by rw [hP.herm.eq]; exact hP.idem
  calc P i i = (Pᴴ * P) i i := by rw [hPP]
    _ = _ := diag_conjTranspose_mul_self P i

omit [DecidableEq N] in
private lemma exists_pos_col {P : Matrix N N ℂ} (h0 : P ≠ 0) :
    ∃ i, 0 < (∑ j, Complex.normSq (P j i)) := by
  obtain ⟨j, i, hji⟩ : ∃ j i, P j i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Matrix.ext fun j i => by simpa using hc j i)
  refine ⟨i, Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ j, by simpa using hji⟩⟩

/-- Expansion of `(F v P)† (F w P)` for linear combinations `F v = ∑ vᵢ Eᵢ` of the errors,
under the Knill–Laflamme conditions. -/
private lemma sandwich_expand {P : Matrix N N ℂ} (hh : P.IsHermitian)
    {E : Fin n → Matrix N N ℂ} (α : Matrix (Fin n) (Fin n) ℂ)
    (hα : ∀ i j, P * (E i)ᴴ * E j * P = α i j • P) (v w : Fin n → ℂ) :
    ((∑ i, v i • E i) * P)ᴴ * ((∑ j, w j • E j) * P)
      = (∑ i, ∑ j, (starRingEnd ℂ (v i)) * w j * α i j) • P := by
  have step : ((∑ i, v i • E i) * P)ᴴ * ((∑ j, w j • E j) * P)
      = ∑ i, ∑ j, ((starRingEnd ℂ (v i)) * w j) • (P * (E i)ᴴ * E j * P) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      hh.eq, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      mul_assoc, RCLike.star_def]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [step, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [hα i j, smul_smul]

/-- The `(k, l)` entry of `uᴴ α u`, written out. -/
private lemma conj_conj_entry (u α : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) :
    (uᴴ * α * u) k l = ∑ i, ∑ j, (starRingEnd ℂ (u i k)) * u j l * α i j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The easy direction -/

/-- If a code corrects an error set, then the Knill–Laflamme conditions hold. -/
theorem knillLaflamme_of_corrects {P : Matrix N N ℂ} (hP : IsCodeProjector P)
    {E : Fin n → Matrix N N ℂ} (h : Corrects P E) : KnillLaflammeConditions P E := by
  obtain ⟨m, R, c, hsum, hRc⟩ := h
  refine ⟨Matrix.of fun i j => ∑ k, (starRingEnd ℂ (c k i)) * c k j, fun i j => ?_⟩
  have key : ∀ k, (P * (E i)ᴴ * (R k)ᴴ) * (R k * E j * P)
      = ((starRingEnd ℂ (c k i)) * c k j) • P := by
    intro k
    have h1' : P * (E i)ᴴ * (R k)ᴴ = (starRingEnd ℂ (c k i)) • P := by
      have := congrArg Matrix.conjTranspose (hRc k i)
      simpa [Matrix.conjTranspose_mul, hP.herm.eq, mul_assoc] using this
    rw [h1', hRc k j, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP.idem]
  have expand : ∑ k, (P * (E i)ᴴ * (R k)ᴴ) * (R k * E j * P)
      = (P * (E i)ᴴ) * (∑ k, (R k)ᴴ * R k) * (E j * P) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_assoc]
  have main : (∑ k, ((starRingEnd ℂ (c k i)) * c k j)) • P
      = (P * (E i)ᴴ) * (∑ k, (R k)ᴴ * R k) * (E j * P) := by
    rw [← expand, Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => (key k).symm
  simpa [mul_assoc] using (by rw [main, hsum, mul_one, mul_assoc] :
    (∑ k, ((starRingEnd ℂ (c k i)) * c k j)) • P = P * (E i)ᴴ * (E j * P)).symm

/-! ### The hard direction -/

/-- If the Knill–Laflamme conditions hold, then the code corrects the error set. -/
theorem corrects_of_knillLaflamme {P : Matrix N N ℂ} (hP : IsCodeProjector P)
    {E : Fin n → Matrix N N ℂ} (h : KnillLaflammeConditions P E) : Corrects P E := by
  obtain ⟨α, hα⟩ := h
  by_cases hP0 : P = 0
  · exact ⟨1, fun _ => 1, fun _ _ => 0, by simp, fun k i => by simp [hP0]⟩
  -- `α` is Hermitian, hence unitarily diagonalizable
  have hHerm : α.IsHermitian := by
    have key : ∀ i j, α j i = starRingEnd ℂ (α i j) := by
      intro i j
      refine smul_cancel_of_ne_zero hP0 (b := starRingEnd ℂ (α i j)) ?_
      have h1 := congrArg Matrix.conjTranspose (hα i j)
      rw [← hα j i]
      simpa [Matrix.conjTranspose_mul, hP.herm.eq, mul_assoc] using h1
    ext i j
    simp [Matrix.conjTranspose_apply, key j i]
  obtain ⟨u, hu_def⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ,
      u = (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  obtain ⟨d, hd_def⟩ : ∃ d : Fin n → ℝ, d = hHerm.eigenvalues := ⟨_, rfl⟩
  have hu2 : u * uᴴ = 1 := by simp [hu_def, ← Matrix.star_eq_conjTranspose]
  have hdiag : uᴴ * α * u = Matrix.diagonal (fun i => (d i : ℂ)) := by
    have := hHerm.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, hu_def, hd_def,
      Function.comp_def] using this
  -- the rotated error operators, restricted to the code
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Matrix N N ℂ, ∀ k, M k = (∑ i, u i k • E i) * P :=
    ⟨_, fun _ => rfl⟩
  have hMM : ∀ k l, (M k)ᴴ * M l = (if k = l then (d k : ℂ) else 0) • P := by
    intro k l
    rw [hM k, hM l, sandwich_expand hP.herm α hα (fun i => u i k) (fun j => u j l)]
    congr 1
    rw [← conj_conj_entry u α k l, hdiag, Matrix.diagonal_apply]
  have hMP : ∀ k, M k * P = M k := by
    intro k
    rw [hM k, mul_assoc, hP.idem]
  have hMzero : ∀ k, d k = 0 → M k = 0 := by
    intro k hk
    refine eq_zero_of_conjTranspose_mul_self ?_
    rw [hMM k k]
    simp [hk]
  -- the eigenvalues are nonnegative
  obtain ⟨i0, hi0⟩ := exists_pos_col hP0
  have hd0 : ∀ k, 0 ≤ d k := by
    intro k
    have hk : (M k)ᴴ * M k = ((d k : ℂ)) • P := by simpa using hMM k k
    have h1 : ((∑ j, Complex.normSq (M k j i0) : ℝ) : ℂ)
        = ((d k * (∑ j, Complex.normSq (P j i0)) : ℝ) : ℂ) := by
      have h0 := congrArg (fun A : Matrix N N ℂ => A i0 i0) hk
      simp only at h0
      rw [diag_conjTranspose_mul_self (M k) i0] at h0
      rw [h0]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [proj_diag hP i0]
      push_cast
      ring
    have h2 : (∑ j, Complex.normSq (M k j i0)) = d k * (∑ j, Complex.normSq (P j i0)) :=
      Complex.ofReal_inj.mp h1
    have h3 : 0 ≤ ∑ j, Complex.normSq (M k j i0) :=
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    nlinarith [hi0, h2, h3]
  -- the recovery Kraus operators
  obtain ⟨s, hs_def⟩ : ∃ s : Fin n → ℝ, ∀ k, s k = Real.sqrt (d k) := ⟨_, fun _ => rfl⟩
  have hss : ∀ k, s k * s k = d k := by
    intro k; rw [hs_def k]; exact Real.mul_self_sqrt (hd0 k)
  have hsinv : ∀ k, (s k)⁻¹ * d k = s k := by
    intro k
    rcases eq_or_ne (s k) 0 with h | h
    · rw [← hss k, h]; simp
    · rw [← hss k]; field_simp
  obtain ⟨R, hR⟩ : ∃ R : Fin n → Matrix N N ℂ, ∀ k, R k = (((s k)⁻¹ : ℝ) : ℂ) • (M k)ᴴ :=
    ⟨_, fun _ => rfl⟩
  have hRH : ∀ k, (R k)ᴴ = (((s k)⁻¹ : ℝ) : ℂ) • M k := by
    intro k
    rw [hR k]
    simp [Matrix.conjTranspose_smul]
  have hRM : ∀ k l, R k * M l = if k = l then ((s k : ℝ) : ℂ) • P else 0 := by
    intro k l
    rw [hR k, Matrix.smul_mul, hMM k l]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, smul_smul, ← Complex.ofReal_mul, hsinv k]
    · simp [hkl]
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin n → Matrix N N ℂ, ∀ k, Q k = (R k)ᴴ * R k := ⟨_, fun _ => rfl⟩
  have hQM : ∀ k l, Q k * M l = if k = l then M k else 0 := by
    intro k l
    rw [hQ k, mul_assoc, hRM k l]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, hRH k, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMP k]
      rcases eq_or_ne (s k) 0 with h0' | h0'
      · have hdk : d k = 0 := by rw [← hss k, h0']; ring
        rw [hMzero k hdk]
        simp
      · rw [← Complex.ofReal_mul, inv_mul_cancel₀ h0']
        simp
    · simp [hkl]
  have hQR : ∀ k l, Q k * (R l)ᴴ = if k = l then (R k)ᴴ else 0 := by
    intro k l
    rw [hRH l, Matrix.mul_smul, hQM k l]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, hRH k]
    · simp [hkl]
  have hQQ : ∀ k l, Q k * Q l = if k = l then Q k else 0 := by
    intro k l
    rw [hQ l, ← mul_assoc, hQR k l]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, hQ k]
    · simp [hkl]
  obtain ⟨T, hT⟩ : ∃ T : Matrix N N ℂ, T = ∑ k, Q k := ⟨_, rfl⟩
  have hTM : ∀ l, T * M l = M l := by
    intro l
    rw [hT, Finset.sum_mul, Finset.sum_congr rfl (fun k _ => hQM k l)]
    simp
  have hTT : T * T = T := by
    conv_lhs => rw [hT]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, hQQ]
    simp [hT]
  have hTH : Tᴴ = T := by
    rw [hT]
    simp [Matrix.conjTranspose_sum, hQ, Matrix.conjTranspose_mul]
  obtain ⟨S, hS⟩ : ∃ S : Matrix N N ℂ, S = 1 - T := ⟨_, rfl⟩
  have hSH : Sᴴ = S := by rw [hS]; simp [hTH]
  have hSS : Sᴴ * S = S := by
    rw [hSH, hS]
    have hexp : (1 - T) * (1 - T) = 1 - T - T + T * T := by noncomm_ring
    rw [hexp, hTT]
    abel
  have hSM : ∀ l, S * M l = 0 := by
    intro l
    rw [hS, sub_mul, one_mul, hTM l, sub_self]
  -- every error, restricted to the code, is a combination of the `M k`
  have hEP : ∀ i, ∑ k, (starRingEnd ℂ (u i k)) • M k = E i * P := by
    intro i
    have e1 : ∀ k, (starRingEnd ℂ (u i k)) • M k
        = ∑ j, ((starRingEnd ℂ (u i k)) * u j k) • (E j * P) := by
      intro k
      rw [hM k]
      simp only [Matrix.sum_mul, Finset.smul_sum, Matrix.smul_mul, smul_smul]
    rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_comm]
    have e2 : ∀ j, ∑ k, ((starRingEnd ℂ (u i k)) * u j k) • (E j * P)
        = ((u * uᴴ) j i) • (E j * P) := by
      intro j
      rw [← Finset.sum_smul]
      congr 1
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl (fun j _ => e2 j), hu2]
    simp [Matrix.one_apply]
  refine ⟨n + 1, Fin.snoc R S,
    Fin.snoc (fun k i => (starRingEnd ℂ (u i k)) * ((s k : ℝ) : ℂ)) 0, ?_, ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hSS, ← hQ, ← hT, hS]
    abel
  · intro k i
    induction k using Fin.lastCases with
    | last =>
        simp only [Fin.snoc_last, Pi.zero_apply, zero_smul]
        rw [mul_assoc, ← hEP i, Finset.mul_sum]
        simp only [Matrix.mul_smul, hSM]
        simp
    | cast j =>
        simp only [Fin.snoc_castSucc]
        rw [mul_assoc, ← hEP i, Finset.mul_sum]
        simp only [Matrix.mul_smul, hRM]
        rw [Finset.sum_eq_single j]
        · rw [if_pos rfl, smul_smul]
        · intro b _ hb
          simp [Ne.symm hb]
        · intro hb
          exact absurd (Finset.mem_univ j) hb

/-- **Knill–Laflamme theorem**: a code with projector `P` corrects an error set `E` if and only
if the Knill–Laflamme conditions hold. -/
theorem knill_laflamme {P : Matrix N N ℂ} (hP : IsCodeProjector P) (E : Fin n → Matrix N N ℂ) :
    Corrects P E ↔ KnillLaflammeConditions P E :=
  ⟨knillLaflamme_of_corrects hP, corrects_of_knillLaflamme hP⟩

end QI

