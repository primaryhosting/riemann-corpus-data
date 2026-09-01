/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/
noncomputable def rtrace (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace X).re

/-- The squared Frobenius norm `Re (tr (Xᴴ X))`. -/
noncomputable def frobSq (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (Xᴴ * X)).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix
(and `0` for a non-Hermitian matrix). -/
noncomputable def posIndex (Q : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  if h : Q.IsHermitian then (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card else 0

/-! ### Basic facts about `rtrace` and `frobSq` -/

lemma rtrace_add (X Y : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (X + Y) = rtrace X + rtrace Y := by
  simp [rtrace, Matrix.trace_add]

lemma rtrace_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (X - Y) = rtrace X - rtrace Y := by
  simp [rtrace, Matrix.trace_sub]

lemma rtrace_mul_comm (X Y : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (X * Y) = rtrace (Y * X) := by
  rw [rtrace, rtrace, Matrix.trace_mul_comm]

lemma frobSq_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ frobSq X := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  simpa [frobSq] using (Complex.le_def.mp h).1

lemma frobSq_add_herm {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) :
    frobSq (X + Y) = frobSq X + 2 * rtrace (X * Y) + frobSq Y := by
  have hxy : Matrix.trace (Yᴴ * X) = Matrix.trace (X * Y) := by
    rw [hY.eq, Matrix.trace_mul_comm]
  simp only [frobSq, rtrace, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re, hX.eq, hxy]
  ring

/-- For positive semidefinite matrices the trace of the product is nonnegative. -/
lemma rtrace_mul_nonneg {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) : 0 ≤ rtrace (X * Y) := by
  obtain ⟨C, rfl⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hX
  obtain ⟨D, rfl⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hY
  have h1 : (Cᴴ * C * (Dᴴ * D)) = (Cᴴ * C * Dᴴ) * D := by
    simp [Matrix.mul_assoc]
  have h2 : D * (Cᴴ * C * Dᴴ) = (C * Dᴴ)ᴴ * (C * Dᴴ) := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h3 := (Matrix.posSemidef_conjTranspose_mul_self (C * Dᴴ)).trace_nonneg
  rw [rtrace, h1, Matrix.trace_mul_comm, h2]
  simpa using (Complex.le_def.mp h3).1

lemma rtrace_nonneg_of_posSemidef {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) :
    0 ≤ rtrace X := by
  simpa [rtrace] using (Complex.le_def.mp hX.trace_nonneg).1

/-- The basic "completing the square" bound against an orthogonal projection. -/
lemma key_proj {X R : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hR : R.IsHermitian)
    (hidem : R * R = R) (t : ℝ) :
    2 * t * rtrace (X * R) ≤ frobSq X + t ^ 2 * rtrace R := by
  set Y : Matrix (Fin d) (Fin d) ℂ := ((-t : ℝ) : ℂ) • R with hY
  have hst : Yᴴ = ((-t : ℝ) : ℂ) • R := by
    rw [hY, Matrix.conjTranspose_smul, hR.eq]; simp
  have hYh : Y.IsHermitian := by rw [Matrix.IsHermitian, hst, hY]
  have h0 : 0 ≤ frobSq (X + Y) := frobSq_nonneg _
  rw [frobSq_add_herm hX hYh] at h0
  have h1 : rtrace (X * Y) = -t * rtrace (X * R) := by
    rw [hY, rtrace, rtrace, Matrix.mul_smul, Matrix.trace_smul]
    simp
  have h2 : frobSq Y = t ^ 2 * rtrace R := by
    have hq : Yᴴ * Y = ((t ^ 2 : ℝ) : ℂ) • R := by
      rw [hst, hY, Matrix.smul_mul, Matrix.mul_smul, hidem, smul_smul]
      push_cast
      ring_nf
    rw [frobSq, hq, Matrix.trace_smul, rtrace, smul_eq_mul, Complex.re_ofReal_mul]
  rw [h1, h2] at h0
  linarith

/-! ### Conjugation by a unitary -/

lemma conj_trace {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1)
    (M : Matrix (Fin d) (Fin d) ℂ) : Matrix.trace (U * M * Uᴴ) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

lemma conj_rtrace {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1)
    (M : Matrix (Fin d) (Fin d) ℂ) : rtrace (U * M * Uᴴ) = rtrace M := by
  rw [rtrace, rtrace, conj_trace hU]

lemma conj_mul {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1)
    (M N : Matrix (Fin d) (Fin d) ℂ) :
    (U * M * Uᴴ) * (U * N * Uᴴ) = U * (M * N) * Uᴴ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U (N * Uᴴ), hU, Matrix.one_mul]

lemma conj_conjTranspose {U : Matrix (Fin d) (Fin d) ℂ} (M : Matrix (Fin d) (Fin d) ℂ) :
    (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma conj_frobSq {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1)
    (M : Matrix (Fin d) (Fin d) ℂ) : frobSq (U * M * Uᴴ) = frobSq M := by
  rw [frobSq, conj_conjTranspose, conj_mul hU, conj_trace hU, frobSq]

lemma conj_posSemidef {U M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) :
    (U * M * Uᴴ).PosSemidef := by
  simpa using hM.conjTranspose_mul_mul_same Uᴴ

/-! ### Spectral tools -/

lemma exists_spectral {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ), ?_, ?_, ?_⟩
  · exact Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  · exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]

lemma diagonal_posSemidef_of_nonneg {f : Fin d → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (diagonal (fun i => ((f i : ℝ) : ℂ))).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  simpa using hf i

lemma rtrace_diagonal (f : Fin d → ℝ) :
    rtrace (diagonal (fun i => ((f i : ℝ) : ℂ))) = ∑ i, f i := by
  simp [rtrace, Matrix.trace_diagonal]

lemma frobSq_diagonal (f : Fin d → ℝ) :
    frobSq (diagonal (fun i => ((f i : ℝ) : ℂ))) = ∑ i, (f i) ^ 2 := by
  rw [frobSq, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace_diagonal, pow_two]

/-- Decomposition of a Hermitian matrix into positive and negative parts, together with
the scalar bound coming from the positive index. -/
lemma exists_pos_neg_parts {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) :
    ∃ Qp Qm : Matrix (Fin d) (Fin d) ℂ, Qp.PosSemidef ∧ Qm.PosSemidef ∧ Q = Qp - Qm ∧
      Qp * Qm = 0 ∧ ∀ c : ℝ, 2 * c * rtrace Qp ≤ frobSq Qp + c ^ 2 * (posIndex Q : ℝ) := by
  obtain ⟨U, hU1, hU2, hspec⟩ := exists_spectral hQ
  set mu : Fin d → ℝ := hQ.eigenvalues with hmu
  set fp : Fin d → ℝ := fun i => max (mu i) 0 with hfp
  set fm : Fin d → ℝ := fun i => max (-(mu i)) 0 with hfm
  refine ⟨U * diagonal (fun i => ((fp i : ℝ) : ℂ)) * Uᴴ,
    U * diagonal (fun i => ((fm i : ℝ) : ℂ)) * Uᴴ,
    conj_posSemidef (diagonal_posSemidef_of_nonneg (fun i => le_max_right _ _)),
    conj_posSemidef (diagonal_posSemidef_of_nonneg (fun i => le_max_right _ _)), ?_, ?_, ?_⟩
  · have hdiff : ∀ i, fp i - fm i = mu i := by
      intro i
      by_cases h : 0 ≤ mu i
      · simp [hfp, hfm, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      · push_neg at h
        simp [hfp, hfm, max_eq_right h.le, max_eq_left (neg_nonneg.mpr h.le)]
    have hd : diagonal (fun i => ((mu i : ℝ) : ℂ))
        = diagonal (fun i => ((fp i : ℝ) : ℂ)) - diagonal (fun i => ((fm i : ℝ) : ℂ)) := by
      rw [Matrix.diagonal_sub]
      congr 1
      funext i
      rw [← Complex.ofReal_sub, hdiff]
    rw [hspec, hd, Matrix.mul_sub, Matrix.sub_mul]
  · rw [conj_mul hU1, Matrix.diagonal_mul_diagonal]
    have hz : (fun i => ((fp i : ℝ) : ℂ) * ((fm i : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul]
      by_cases h : 0 ≤ mu i
      · simp [hfm, max_eq_right (neg_nonpos.mpr h)]
      · push_neg at h
        simp [hfp, max_eq_right h.le]
    rw [hz]
    simp
  · intro c
    rw [conj_rtrace hU1, conj_frobSq hU1, rtrace_diagonal, frobSq_diagonal]
    have hpi : (posIndex Q : ℝ) = ∑ i, (if 0 < mu i then (1 : ℝ) else 0) := by
      rw [posIndex, dif_pos hQ, ← hmu]
      simp [Finset.sum_boole]
    rw [hpi, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases h : 0 < mu i
    · have hfpi : fp i = mu i := by simp [hfp, max_eq_left h.le]
      rw [hfpi, if_pos h]
      nlinarith [sq_nonneg (mu i - c)]
    · have hfpi : fp i = 0 := by simp [hfp, max_eq_right (not_lt.mp h)]
      rw [hfpi, if_neg h]
      simp

/-- The orthogonal projection onto the range of a positive semidefinite matrix. -/
lemma exists_range_proj {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef) :
    ∃ R : Matrix (Fin d) (Fin d) ℂ, R.IsHermitian ∧ R * R = R ∧ P * R = P ∧
      (1 - R).PosSemidef ∧ rtrace R = (P.rank : ℝ) := by
  obtain ⟨V, hV1, hV2, hspec⟩ := exists_spectral hP.1
  set p : Fin d → ℝ := hP.1.eigenvalues with hp
  set e : Fin d → ℝ := fun i => if p i ≠ 0 then 1 else 0 with he
  have hstar : (diagonal (fun i => ((e i : ℝ) : ℂ)))ᴴ = diagonal (fun i => ((e i : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hee : (fun i => ((e i : ℝ) : ℂ) * ((e i : ℝ) : ℂ)) = fun i => ((e i : ℝ) : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul]
    congr 1
    by_cases h : p i = 0 <;> simp [he, h]
  have hpe : (fun i => ((p i : ℝ) : ℂ) * ((e i : ℝ) : ℂ)) = fun i => ((p i : ℝ) : ℂ) := by
    funext i
    rw [← Complex.ofReal_mul]
    congr 1
    by_cases h : p i = 0 <;> simp [he, h]
  refine ⟨V * diagonal (fun i => ((e i : ℝ) : ℂ)) * Vᴴ, ?_, ?_, ?_, ?_, ?_⟩
  · show (V * diagonal (fun i => ((e i : ℝ) : ℂ)) * Vᴴ)ᴴ = _
    rw [conj_conjTranspose, hstar]
  · rw [conj_mul hV1, Matrix.diagonal_mul_diagonal, hee]
  · rw [hspec, conj_mul hV1, Matrix.diagonal_mul_diagonal, hpe]
  · have hone : (1 : Matrix (Fin d) (Fin d) ℂ) = V * (1 : Matrix (Fin d) (Fin d) ℂ) * Vᴴ := by
      rw [Matrix.mul_one, hV2]
    have hsub : (1 : Matrix (Fin d) (Fin d) ℂ) - V * diagonal (fun i => ((e i : ℝ) : ℂ)) * Vᴴ
        = V * diagonal (fun i => (((1 - e i : ℝ)) : ℂ)) * Vᴴ := by
      have hdd : diagonal (fun i => (((1 - e i : ℝ)) : ℂ))
          = (1 : Matrix (Fin d) (Fin d) ℂ) - diagonal (fun i => ((e i : ℝ) : ℂ)) := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
        congr 1
        funext i
        simp
      rw [hdd, Matrix.mul_sub, Matrix.sub_mul, ← hone]
    rw [hsub]
    refine conj_posSemidef (diagonal_posSemidef_of_nonneg ?_)
    intro i
    by_cases h : p i = 0 <;> simp [he, h]
  · rw [conj_rtrace hV1, rtrace_diagonal, hP.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
      ← hp]
    have hcongr : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        e i = if ¬ p i = 0 then (1 : ℝ) else 0 := by
      intro i _
      by_cases h : p i = 0 <;> simp [he, h]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite, Finset.sum_const]
    simp

/-! ### The rank-trace inequality -/

/-- **Rank-trace inequality.** For `P` positive semidefinite with `rank P ≤ r` and `Q`
Hermitian with at most `b` strictly positive eigenvalues, and any `c > 0`,
`c * tr P - (c²/4) r + 2c * tr Q - c² b ≤ ‖P + Q‖_F²`. -/
theorem rank_trace_ineq {P Q : Matrix (Fin d) (Fin d) ℂ} {r b c : ℝ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hr : (P.rank : ℝ) ≤ r) (hb : (posIndex Q : ℝ) ≤ b) (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  obtain ⟨Qp, Qm, hQp, hQm, hQeq, hQpm, hQbound⟩ := exists_pos_neg_parts hQ
  obtain ⟨R, hRh, hRidem, hPR, hRc, hRtr⟩ := exists_range_proj hP
  set B : Matrix (Fin d) (Fin d) ℂ := P - Qm with hB
  have hBh : B.IsHermitian := hP.1.sub hQm.1
  have hsum : P + Q = B + Qp := by rw [hQeq, hB]; abel
  have hexp : frobSq (P + Q) = frobSq B + 2 * rtrace (B * Qp) + frobSq Qp := by
    rw [hsum, frobSq_add_herm hBh hQp.1]
  have hmz : rtrace (Qm * Qp) = 0 := by
    rw [rtrace_mul_comm, hQpm]
    simp [rtrace]
  have hint : rtrace (B * Qp) = rtrace (P * Qp) := by
    rw [hB, Matrix.sub_mul, rtrace_sub, hmz, sub_zero]
  have hint0 : 0 ≤ rtrace (P * Qp) := rtrace_mul_nonneg hP hQp
  have hmat : B * R - B = Qm * (1 - R) := by
    rw [hB, Matrix.sub_mul, hPR, Matrix.mul_sub, Matrix.mul_one]
    abel
  have hBproj : rtrace B ≤ rtrace (B * R) := by
    have h1 : rtrace (B * R) - rtrace B = rtrace (Qm * (1 - R)) := by
      rw [← rtrace_sub, hmat]
    have h2 : 0 ≤ rtrace (Qm * (1 - R)) := rtrace_mul_nonneg hQm hRc
    linarith
  have hAbound : c * rtrace B ≤ frobSq B + c ^ 2 / 4 * (P.rank : ℝ) := by
    have h := key_proj hBh hRh hRidem (c / 2)
    rw [hRtr] at h
    have h3 : c * rtrace B ≤ c * rtrace (B * R) :=
      mul_le_mul_of_nonneg_left hBproj hc.le
    have h4 : 2 * (c / 2) * rtrace (B * R) = c * rtrace (B * R) := by ring
    have h5 : (c / 2) ^ 2 * (P.rank : ℝ) = c ^ 2 / 4 * (P.rank : ℝ) := by ring
    rw [h4, h5] at h
    linarith
  have hQb := hQbound c
  have htrP : rtrace B = rtrace P - rtrace Qm := by rw [hB, rtrace_sub]
  have htrQ : rtrace Q = rtrace Qp - rtrace Qm := by rw [hQeq, rtrace_sub]
  have hQm0 : 0 ≤ rtrace Qm := rtrace_nonneg_of_posSemidef hQm
  have hrs : c ^ 2 / 4 * (P.rank : ℝ) ≤ c ^ 2 / 4 * r :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have hbs : c ^ 2 * (posIndex Q : ℝ) ≤ c ^ 2 * b :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hcm : 0 ≤ c * rtrace Qm := mul_nonneg hc.le hQm0
  have e1 : c * rtrace B = c * rtrace P - c * rtrace Qm := by rw [htrP]; ring
  have e2 : 2 * c * rtrace Qp = 2 * c * rtrace Q + 2 * c * rtrace Qm := by rw [htrQ]; ring
  rw [e1] at hAbound
  rw [e2] at hQb
  rw [hexp, hint]
  linarith

/-- The special case `c = 2` of the rank-trace inequality. -/
theorem rank_trace_ineq_two {P Q : Matrix (Fin d) (Fin d) ℂ} {r b : ℝ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hr : (P.rank : ℝ) ≤ r) (hb : (posIndex Q : ℝ) ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  norm_num at this ⊢
  linarith

end Zeta23Redux.LinAlg

