import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/
noncomputable def bellState : Fin 2 × Fin 2 → ℂ :=
  fun x => if x.1 = x.2 then ((Real.sqrt 2)⁻¹ : ℝ) else 0

lemma bellState_normalized : ∑ x, ‖bellState x‖ ^ 2 = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, bellState, Complex.norm_real]
  field_simp
  linarith [h2]

/-- An explicit Schmidt decomposition of the Bell state. -/
noncomputable def bellSchmidt : SchmidtDecomp bellState where
  rank := 2
  lam := fun _ => (Real.sqrt 2)⁻¹
  e := fun k i => if i = k then 1 else 0
  f := fun k j => if j = k then 1 else 0
  lam_pos := fun _ => by positivity
  e_orthonormal := by
    intro k l
    simp [Finset.sum_ite_eq, eq_comm]
  f_orthonormal := by
    intro k l
    simp [Finset.sum_ite_eq, eq_comm]
  eq_sum := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [bellState]

/-- The Schmidt coefficients of the Bell state are `1/√2, 1/√2`. -/
theorem bellState_coeffs (D : SchmidtDecomp bellState) :
    D.coeffs = {(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹} := by
  have h := (schmidt_decomposition bellState bellState_normalized).2 D bellSchmidt
  rw [h]
  rfl

end QI

import Mathlib

/-!
# The Schmidt decomposition of a bipartite pure state

A bipartite pure state on `ℂ^m ⊗ ℂ^n` is modelled as a normalized vector
`psi : Fin m × Fin n → ℂ`.  A *Schmidt decomposition* of `psi` consists of a rank `r`,
positive reals `lam k` (the Schmidt coefficients), and orthonormal families `e k` in `ℂ^m`
and `f k` in `ℂ^n` such that `psi (i, j) = ∑ k, lam k * e k i * f k j`.

The main result `QI.schmidt_decomposition` states that every bipartite pure state admits
such a decomposition, and that the multiset of Schmidt coefficients is uniquely determined.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {m n : ℕ}

/-- `v` is an orthonormal family of vectors in `ℂ^d`. -/
def IsONFamily {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → (Fin d → ℂ)) : Prop :=
  ∀ k l, ∑ i, (starRingEnd ℂ) (v k i) * v l i = if k = l then 1 else 0

/-- A Schmidt decomposition of the bipartite pure state `psi`. -/
structure SchmidtDecomp (psi : Fin m × Fin n → ℂ) where
  /-- The Schmidt rank. -/
  rank : ℕ
  /-- The Schmidt coefficients. -/
  lam : Fin rank → ℝ
  /-- The orthonormal family on the first factor. -/
  e : Fin rank → (Fin m → ℂ)
  /-- The orthonormal family on the second factor. -/
  f : Fin rank → (Fin n → ℂ)
  lam_pos : ∀ k, 0 < lam k
  e_orthonormal : IsONFamily e
  f_orthonormal : IsONFamily f
  eq_sum : ∀ i j, psi (i, j) = ∑ k, (lam k : ℂ) * e k i * f k j

/-- The multiset of Schmidt coefficients of a Schmidt decomposition. -/
def SchmidtDecomp.coeffs {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) : Multiset ℝ :=
  Multiset.map D.lam Finset.univ.val

/-! ### Multisets of positive reals are determined by their power sums -/

theorem tendsto_multiset_pow_sum_zero {S : Multiset ℝ} {a : ℝ} (ha : 0 < a)
    (h : ∀ x ∈ S, 0 ≤ x ∧ x < a) :
    Filter.Tendsto (fun p : ℕ => (S.map (fun s => (s / a) ^ p)).sum) Filter.atTop (nhds 0) := by
  revert h
  induction S using Multiset.induction_on with
  | empty => intro _; simp
  | cons b S ih =>
      intro h
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have hb := h b (Multiset.mem_cons_self b S)
      have h1 : Filter.Tendsto (fun p : ℕ => (b / a) ^ p) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hb.1 ha.le) ((div_lt_one ha).2 hb.2)
      have h2 := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      simpa using h1.add h2

lemma multiset_sum_map_div_pow (S : Multiset ℝ) (a : ℝ) (p : ℕ) :
    (S.map (fun s => (s / a) ^ p)).sum = (S.map (· ^ p)).sum / a ^ p := by
  rw [div_eq_mul_inv, ← Multiset.sum_map_mul_right]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => by
    rw [div_pow, div_eq_mul_inv])

/-- Two multisets of positive reals with the same power sums are equal. -/
theorem multiset_eq_of_powerSum_eq {S T : Multiset ℝ} (hS : ∀ x ∈ S, 0 < x)
    (hT : ∀ x ∈ T, 0 < x)
    (h : ∀ p : ℕ, 1 ≤ p → (S.map (· ^ p)).sum = (T.map (· ^ p)).sum) : S = T := by
  classical
  generalize hN : S.card + T.card = N
  induction N using Nat.strong_induction_on generalizing S T with
  | _ N IH =>
    by_cases hST : S + T = 0
    · rw [AddLeftCancelMonoid.add_eq_zero] at hST
      rw [hST.1, hST.2]
    · obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hST
      have hUne : (S + T).toFinset.Nonempty := ⟨z, Multiset.mem_toFinset.2 hz⟩
      set a := (S + T).toFinset.max' hUne with ha_def
      have ha_mem : a ∈ S + T := Multiset.mem_toFinset.1 ((S + T).toFinset.max'_mem hUne)
      have hapos : 0 < a := by
        rcases Multiset.mem_add.1 ha_mem with h' | h'
        · exact hS a h'
        · exact hT a h'
      have hle : ∀ x ∈ S + T, x ≤ a := fun x hx =>
        (S + T).toFinset.le_max' x (Multiset.mem_toFinset.2 hx)
      -- split off the copies of `a`
      set cS := S.count a with hcS
      set cT := T.count a with hcT
      set S' := S.filter (fun x => ¬ x = a) with hS'
      set T' := T.filter (fun x => ¬ x = a) with hT'
      have hSsplit : Multiset.replicate cS a + S' = S := by
        rw [hS', hcS, ← Multiset.filter_eq' S a]
        exact Multiset.filter_add_not _ S
      have hTsplit : Multiset.replicate cT a + T' = T := by
        rw [hT', hcT, ← Multiset.filter_eq' T a]
        exact Multiset.filter_add_not _ T
      have hS'pos : ∀ x ∈ S', 0 < x := fun x hx => hS x (Multiset.mem_of_mem_filter hx)
      have hT'pos : ∀ x ∈ T', 0 < x := fun x hx => hT x (Multiset.mem_of_mem_filter hx)
      have hS'lt : ∀ x ∈ S', 0 ≤ x ∧ x < a := by
        intro x hx
        refine ⟨(hS'pos x hx).le, lt_of_le_of_ne (hle x (Multiset.mem_add.2 (Or.inl
          (Multiset.mem_of_mem_filter hx)))) ?_⟩
        exact (Multiset.mem_filter.1 hx).2
      have hT'lt : ∀ x ∈ T', 0 ≤ x ∧ x < a := by
        intro x hx
        refine ⟨(hT'pos x hx).le, lt_of_le_of_ne (hle x (Multiset.mem_add.2 (Or.inr
          (Multiset.mem_of_mem_filter hx)))) ?_⟩
        exact (Multiset.mem_filter.1 hx).2
      -- power sums split
      have hsplitS : ∀ p : ℕ, (S.map (· ^ p)).sum = cS * a ^ p + (S'.map (· ^ p)).sum := by
        intro p
        rw [← hSsplit]
        simp [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
      have hsplitT : ∀ p : ℕ, (T.map (· ^ p)).sum = cT * a ^ p + (T'.map (· ^ p)).sum := by
        intro p
        rw [← hTsplit]
        simp [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
      -- the counts agree
      have hcount : cS = cT := by
        have key : ∀ p : ℕ, 1 ≤ p →
            (cS : ℝ) + (S'.map (fun s => (s / a) ^ p)).sum
              = (cT : ℝ) + (T'.map (fun s => (s / a) ^ p)).sum := by
          intro p hp
          have hap : (a : ℝ) ^ p ≠ 0 := by positivity
          have := h p hp
          rw [hsplitS p, hsplitT p] at this
          rw [multiset_sum_map_div_pow, multiset_sum_map_div_pow]
          field_simp
          linarith [this]
        have t1 : Filter.Tendsto
            (fun p : ℕ => (cS : ℝ) + (S'.map (fun s => (s / a) ^ p)).sum)
            Filter.atTop (nhds (cS : ℝ)) := by
          simpa using tendsto_const_nhds.add (tendsto_multiset_pow_sum_zero hapos hS'lt)
        have t2 : Filter.Tendsto
            (fun p : ℕ => (cT : ℝ) + (T'.map (fun s => (s / a) ^ p)).sum)
            Filter.atTop (nhds (cT : ℝ)) := by
          simpa using tendsto_const_nhds.add (tendsto_multiset_pow_sum_zero hapos hT'lt)
        have t1' : Filter.Tendsto
            (fun p : ℕ => (cT : ℝ) + (T'.map (fun s => (s / a) ^ p)).sum)
            Filter.atTop (nhds (cS : ℝ)) := by
          refine t1.congr' ?_
          filter_upwards [Filter.eventually_ge_atTop 1] with p hp using key p hp
        have : (cS : ℝ) = (cT : ℝ) := tendsto_nhds_unique t1' t2
        exact_mod_cast this
      -- the counts are positive
      have hcSpos : 1 ≤ cS := by
        have : 0 < Multiset.count a (S + T) := Multiset.count_pos.2 ha_mem
        rw [Multiset.count_add, ← hcS, ← hcT, ← hcount] at this
        omega
      -- apply the induction hypothesis
      have hcard : S'.card + T'.card < N := by
        have h1 : S'.card + cS = S.card := by
          rw [← hSsplit]; simp [Multiset.card_add, Multiset.card_replicate]; omega
        have h2 : T'.card + cT = T.card := by
          rw [← hTsplit]; simp [Multiset.card_add, Multiset.card_replicate]; omega
        omega
      have hpow : ∀ p : ℕ, 1 ≤ p → (S'.map (· ^ p)).sum = (T'.map (· ^ p)).sum := by
        intro p hp
        have := h p hp
        rw [hsplitS p, hsplitT p, hcount] at this
        linarith
      have := IH (S'.card + T'.card) hcard hS'pos hT'pos hpow rfl
      rw [← hSsplit, ← hTsplit, this, hcount]

/-! ### The reduced density matrix -/

/-- The reduced density matrix of `psi` on the first factor. -/
noncomputable def rho (psi : Fin m × Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i i' => ∑ j, psi (i, j) * (starRingEnd ℂ) (psi (i', j))

lemma rho_eq_mul_conjTranspose (psi : Fin m × Fin n → ℂ) :
    rho psi = (Matrix.of fun i j => psi (i, j)) * (Matrix.of fun i j => psi (i, j))ᴴ := by
  ext i i'
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rho]

lemma rho_posSemidef (psi : Fin m × Fin n → ℂ) : (rho psi).PosSemidef := by
  rw [rho_eq_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma trace_rho (psi : Fin m × Fin n → ℂ) :
    (rho psi).trace = ((∑ x, ‖psi x‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.diag, rho, Fintype.sum_prod_type, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

lemma rho_apply_of_decomp {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) (i i' : Fin m) :
    rho psi i i' = ∑ k, ((D.lam k : ℂ) ^ 2) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
  have hf := D.f_orthonormal
  show (∑ j, psi (i, j) * (starRingEnd ℂ) (psi (i', j))) = _
  calc ∑ j, psi (i, j) * (starRingEnd ℂ) (psi (i', j))
      = ∑ j, (∑ k, (D.lam k : ℂ) * D.e k i * D.f k j) *
          (∑ l, (starRingEnd ℂ) ((D.lam l : ℂ) * D.e l i' * D.f l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [D.eq_sum i j, D.eq_sum i' j, map_sum]
    _ = ∑ j, ∑ k, ∑ l, ((D.lam k : ℂ) * D.e k i * D.f k j) *
          (starRingEnd ℂ) ((D.lam l : ℂ) * D.e l i' * D.f l j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ k, ∑ l, ∑ j, ((D.lam k : ℂ) * D.e k i * D.f k j) *
          (starRingEnd ℂ) ((D.lam l : ℂ) * D.e l i' * D.f l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ((D.lam k : ℂ) * (D.lam l : ℂ) * D.e k i * (starRingEnd ℂ) (D.e l i')) *
          (∑ j, (starRingEnd ℂ) (D.f l j) * D.f k j) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∑ k, ((D.lam k : ℂ) ^ 2) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [hf l k]]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring

lemma pow_rho_apply {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) :
    ∀ p : ℕ, ∀ i i' : Fin m,
      ((rho psi) ^ (p + 1)) i i' =
        ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
  have he := D.e_orthonormal
  intro p
  induction p with
  | zero =>
      intro i i'
      rw [pow_one]
      simpa using rho_apply_of_decomp D i i'
  | succ q ih =>
      intro i i'
      rw [pow_succ, Matrix.mul_apply]
      calc ∑ x, ((rho psi) ^ (q + 1)) i x * (rho psi) x i'
          = ∑ x, (∑ k, ((D.lam k : ℂ) ^ (2 * (q + 1))) * D.e k i * (starRingEnd ℂ) (D.e k x)) *
              (∑ l, ((D.lam l : ℂ) ^ 2) * D.e l x * (starRingEnd ℂ) (D.e l i')) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [ih i x, rho_apply_of_decomp D x i']
        _ = ∑ x, ∑ k, ∑ l, (((D.lam k : ℂ) ^ (2 * (q + 1))) * D.e k i * (starRingEnd ℂ) (D.e k x)) *
              (((D.lam l : ℂ) ^ 2) * D.e l x * (starRingEnd ℂ) (D.e l i')) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_mul_sum]
        _ = ∑ k, ∑ l, ∑ x, (((D.lam k : ℂ) ^ (2 * (q + 1))) * D.e k i * (starRingEnd ℂ) (D.e k x)) *
              (((D.lam l : ℂ) ^ 2) * D.e l x * (starRingEnd ℂ) (D.e l i')) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
        _ = ∑ k, ∑ l, (((D.lam k : ℂ) ^ (2 * (q + 1))) * ((D.lam l : ℂ) ^ 2) * D.e k i *
              (starRingEnd ℂ) (D.e l i')) * (∑ x, (starRingEnd ℂ) (D.e k x) * D.e l x) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
        _ = ∑ k, ((D.lam k : ℂ) ^ (2 * (q + 1 + 1))) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [he k l]]
            simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
            ring

lemma trace_pow_rho {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) (p : ℕ) :
    ((rho psi) ^ (p + 1)).trace = ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) := by
  have he := D.e_orthonormal
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc ∑ i, ((rho psi) ^ (p + 1)) i i
      = ∑ i, ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) * D.e k i * (starRingEnd ℂ) (D.e k i) := by
        exact Finset.sum_congr rfl fun i _ => pow_rho_apply D p i i
    _ = ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) * (∑ i, (starRingEnd ℂ) (D.e k i) * D.e k i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [he k k]
        simp

/-- The power sums of the squared Schmidt coefficients are determined by `psi`. -/
lemma sum_lam_pow {psi : Fin m × Fin n → ℂ} (D D' : SchmidtDecomp psi) (p : ℕ) (hp : 1 ≤ p) :
    ∑ k, (D.lam k ^ 2) ^ p = ∑ k, (D'.lam k ^ 2) ^ p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have cast_sum : ∀ E : SchmidtDecomp psi,
      ((∑ k, (E.lam k ^ 2) ^ (q + 1) : ℝ) : ℂ) = ∑ k, ((E.lam k : ℂ) ^ (2 * (q + 1))) := by
    intro E
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [← pow_mul]
  have : ((∑ k, (D.lam k ^ 2) ^ (q + 1) : ℝ) : ℂ) = ((∑ k, (D'.lam k ^ 2) ^ (q + 1) : ℝ) : ℂ) := by
    rw [cast_sum D, cast_sum D', ← trace_pow_rho D q, ← trace_pow_rho D' q]
  exact_mod_cast this

/-! ### Existence -/

section Existence

variable (psi : Fin m × Fin n → ℂ)

/-- Eigenvalues of the reduced density matrix. -/
noncomputable def eigMu : Fin m → ℝ := (rho_posSemidef psi).isHermitian.eigenvalues

/-- An orthonormal eigenbasis of the reduced density matrix. -/
noncomputable def eigVec (k : Fin m) : Fin m → ℂ := fun i =>
  ((rho_posSemidef psi).isHermitian.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) i k

lemma eigMu_nonneg (k : Fin m) : 0 ≤ eigMu psi k :=
  (rho_posSemidef psi).eigenvalues_nonneg k

lemma eigVec_orthonormal (k l : Fin m) :
    ∑ i, (starRingEnd ℂ) (eigVec psi k i) * eigVec psi l i = if k = l then 1 else 0 := by
  have h := Matrix.UnitaryGroup.star_mul_self
    (rho_posSemidef psi).isHermitian.eigenvectorUnitary
  have := congrFun (congrFun h k) l
  simpa [Matrix.mul_apply, Matrix.one_apply, eigVec] using this

lemma eigVec_complete (i i' : Fin m) :
    ∑ k, eigVec psi k i * (starRingEnd ℂ) (eigVec psi k i') = if i = i' then 1 else 0 := by
  have h := Unitary.coe_mul_star_self
    (rho_posSemidef psi).isHermitian.eigenvectorUnitary
  have := congrFun (congrFun h i) i'
  simpa [Matrix.mul_apply, Matrix.one_apply, eigVec] using this

lemma rho_mulVec_eigVec (k i : Fin m) :
    ∑ i', rho psi i i' * eigVec psi k i' = (eigMu psi k : ℂ) * eigVec psi k i := by
  have h := (rho_posSemidef psi).isHermitian.mulVec_eigenvectorBasis k
  have := congrFun h i
  simpa [Matrix.mulVec, dotProduct, eigVec, eigMu, Complex.real_smul, mul_comm] using this

/-- The (unnormalized) vectors on the second factor. -/
noncomputable def wvec (k : Fin m) : Fin n → ℂ := fun j =>
  ∑ i, (starRingEnd ℂ) (eigVec psi k i) * psi (i, j)

lemma wvec_inner (k l : Fin m) :
    ∑ j, (starRingEnd ℂ) (wvec psi k j) * wvec psi l j =
      if k = l then (eigMu psi k : ℂ) else 0 := by
  calc ∑ j, (starRingEnd ℂ) (wvec psi k j) * wvec psi l j
      = ∑ j, (∑ i, eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          (∑ i', (starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [wvec, map_sum, map_mul, Complex.conj_conj]
    _ = ∑ j, ∑ i, ∑ i', (eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          ((starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ i, ∑ i', ∑ j, (eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          ((starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ i', ∑ i, ∑ j, (eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          ((starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        rw [Finset.sum_comm]
    _ = ∑ i', (starRingEnd ℂ) (eigVec psi l i') * (∑ i, rho psi i' i * eigVec psi k i) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show _ = (starRingEnd ℂ) (eigVec psi l i') *
          ((∑ j, psi (i', j) * (starRingEnd ℂ) (psi (i, j))) * eigVec psi k i)
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = if k = l then (eigMu psi k : ℂ) else 0 := by
        have : ∀ i', (starRingEnd ℂ) (eigVec psi l i') * (∑ i, rho psi i' i * eigVec psi k i)
            = (eigMu psi k : ℂ) * ((starRingEnd ℂ) (eigVec psi l i') * eigVec psi k i') := by
          intro i'
          rw [rho_mulVec_eigVec]
          ring
        rw [Finset.sum_congr rfl fun i' (_ : i' ∈ Finset.univ) => this i', ← Finset.mul_sum,
          eigVec_orthonormal psi l k]
        by_cases h : k = l
        · simp [h]
        · simp [h, Ne.symm h]

lemma wvec_eq_zero (k : Fin m) (hk : eigMu psi k = 0) : wvec psi k = 0 := by
  have h := wvec_inner psi k k
  rw [if_pos rfl, hk] at h
  have h' : ∑ j, (starRingEnd ℂ) (wvec psi k j) * wvec psi k j = 0 := by simpa using h
  have h2 : ((∑ j, ‖wvec psi k j‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← h']
    push_cast
    refine (Finset.sum_congr rfl fun j _ => ?_).symm
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h3 : ∑ j, ‖wvec psi k j‖ ^ 2 = 0 := by exact_mod_cast h2
  have h4 : ∀ j ∈ (Finset.univ : Finset (Fin n)), ‖wvec psi k j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h3
  funext j
  have := h4 j (Finset.mem_univ j)
  have : ‖wvec psi k j‖ = 0 := by nlinarith [norm_nonneg (wvec psi k j)]
  simpa using this

lemma psi_eq_sum (i : Fin m) (j : Fin n) :
    psi (i, j) = ∑ k, eigVec psi k i * wvec psi k j := by
  symm
  calc ∑ k, eigVec psi k i * wvec psi k j
      = ∑ k, ∑ i', eigVec psi k i * ((starRingEnd ℂ) (eigVec psi k i') * psi (i', j)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [wvec, Finset.mul_sum]
    _ = ∑ i', ∑ k, eigVec psi k i * ((starRingEnd ℂ) (eigVec psi k i') * psi (i', j)) := by
        rw [Finset.sum_comm]
    _ = ∑ i', (∑ k, eigVec psi k i * (starRingEnd ℂ) (eigVec psi k i')) * psi (i', j) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = psi (i, j) := by
        rw [Finset.sum_congr rfl fun i' (_ : i' ∈ Finset.univ) => by
          rw [eigVec_complete psi i i']]
        simp

end Existence

lemma exists_schmidtDecomp (psi : Fin m × Fin n → ℂ) : Nonempty (SchmidtDecomp psi) := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun k => eigMu psi k ≠ 0) with hSdef
  set kk : Fin S.card → Fin m := fun t => ((S.equivFin.symm t : S) : Fin m) with hkkdef
  have hkk_mem : ∀ t, kk t ∈ S := fun t => (S.equivFin.symm t).2
  have hkk_inj : Function.Injective kk := by
    intro a b hab
    have h1 : (S.equivFin.symm a) = (S.equivFin.symm b) := Subtype.ext hab
    simpa using congrArg S.equivFin h1
  have hmu_ne : ∀ t, eigMu psi (kk t) ≠ 0 := by
    intro t
    have := hkk_mem t
    rw [hSdef, Finset.mem_filter] at this
    exact this.2
  have hmu_pos : ∀ t, 0 < eigMu psi (kk t) := fun t =>
    lt_of_le_of_ne (eigMu_nonneg psi (kk t)) (Ne.symm (hmu_ne t))
  have hsqrt_pos : ∀ t, 0 < Real.sqrt (eigMu psi (kk t)) := fun t => Real.sqrt_pos.2 (hmu_pos t)
  have hsqrt_sq : ∀ t, Real.sqrt (eigMu psi (kk t)) ^ 2 = eigMu psi (kk t) := fun t =>
    Real.sq_sqrt (eigMu_nonneg psi (kk t))
  refine ⟨{ rank := S.card
            lam := fun t => Real.sqrt (eigMu psi (kk t))
            e := fun t => eigVec psi (kk t)
            f := fun t j => ((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * wvec psi (kk t) j
            lam_pos := hsqrt_pos
            e_orthonormal := ?_
            f_orthonormal := ?_
            eq_sum := ?_ }⟩
  · intro t s
    rw [eigVec_orthonormal]
    by_cases h : t = s
    · simp [h]
    · rw [if_neg (fun hc => h (hkk_inj hc)), if_neg h]
  · intro t s
    have hct : ((Real.sqrt (eigMu psi (kk t)) : ℂ)) ≠ 0 := by
      simpa using (hsqrt_pos t).ne'
    have hcs : ((Real.sqrt (eigMu psi (kk s)) : ℂ)) ≠ 0 := by
      simpa using (hsqrt_pos s).ne'
    have hstep : ∑ j, (starRingEnd ℂ) (((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * wvec psi (kk t) j) *
        (((Real.sqrt (eigMu psi (kk s)) : ℂ))⁻¹ * wvec psi (kk s) j)
        = (((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * ((Real.sqrt (eigMu psi (kk s)) : ℂ))⁻¹) *
          ∑ j, (starRingEnd ℂ) (wvec psi (kk t) j) * wvec psi (kk s) j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    rw [hstep, wvec_inner]
    by_cases h : t = s
    · subst h
      rw [if_pos rfl]
      field_simp
      rw [← Complex.ofReal_pow, hsqrt_sq t]
      simp
    · rw [if_neg (fun hc => h (hkk_inj hc)), if_neg h, mul_zero]
  · intro i j
    have hterm : ∀ t : Fin S.card,
        ((Real.sqrt (eigMu psi (kk t)) : ℝ) : ℂ) * eigVec psi (kk t) i *
          (((Real.sqrt (eigMu psi (kk t)) : ℂ))⁻¹ * wvec psi (kk t) j)
          = eigVec psi (kk t) i * wvec psi (kk t) j := by
      intro t
      have hct : ((Real.sqrt (eigMu psi (kk t)) : ℂ)) ≠ 0 := by
        simpa using (hsqrt_pos t).ne'
      field_simp
    rw [Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hterm t]
    have hre : ∑ t : Fin S.card, eigVec psi (kk t) i * wvec psi (kk t) j
        = ∑ k ∈ S, eigVec psi k i * wvec psi k j := by
      rw [Equiv.sum_comp S.equivFin.symm (fun x : S => eigVec psi (x : Fin m) i *
        wvec psi (x : Fin m) j)]
      exact Finset.sum_coe_sort S (fun k => eigVec psi k i * wvec psi k j)
    rw [hre]
    have hall : ∑ k ∈ S, eigVec psi k i * wvec psi k j
        = ∑ k : Fin m, eigVec psi k i * wvec psi k j := by
      refine Finset.sum_subset (Finset.subset_univ S) fun k _ hk => ?_
      have hk0 : eigMu psi k = 0 := by
        rw [hSdef, Finset.mem_filter] at hk
        simpa using not_and.1 hk (Finset.mem_univ k)
      rw [wvec_eq_zero psi k hk0]
      simp
    rw [hall]
    exact psi_eq_sum psi i j

/-! ### Main theorem -/

/-- **Schmidt decomposition**: every bipartite pure state `psi` on `ℂ^m ⊗ ℂ^n` admits a
decomposition `psi (i, j) = ∑ k, lam k * e k i * f k j` with positive Schmidt coefficients
`lam k` (whose squares sum to `1`) and orthonormal families `e`, `f`; moreover the multiset
of Schmidt coefficients is the same for any two such decompositions. -/
theorem schmidt_decomposition (psi : Fin m × Fin n → ℂ) (hpsi : ∑ x, ‖psi x‖ ^ 2 = 1) :
    (∃ D : SchmidtDecomp psi, ∑ k, D.lam k ^ 2 = 1) ∧
      ∀ D D' : SchmidtDecomp psi, D.coeffs = D'.coeffs := by
  constructor
  · obtain ⟨D⟩ := exists_schmidtDecomp psi
    refine ⟨D, ?_⟩
    have h1 := trace_pow_rho D 0
    rw [pow_one, trace_rho, hpsi] at h1
    have : ∑ k, ((D.lam k : ℂ)) ^ 2 = 1 := by
      rw [← h1]; norm_num
    exact_mod_cast this
  · intro D D'
    have hsum : ∀ (E : SchmidtDecomp psi) (p : ℕ),
        ((Multiset.map (· ^ 2) E.coeffs).map (· ^ p)).sum = ∑ k, (E.lam k ^ 2) ^ p := by
      intro E p
      simp [SchmidtDecomp.coeffs, Function.comp_def, Finset.sum]
    have hpos : ∀ (E : SchmidtDecomp psi), ∀ x ∈ Multiset.map (· ^ 2) E.coeffs, 0 < x := by
      intro E x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hy
      exact pow_pos (E.lam_pos k) 2
    have key : Multiset.map (· ^ 2) D.coeffs = Multiset.map (· ^ 2) D'.coeffs := by
      refine multiset_eq_of_powerSum_eq (hpos D) (hpos D') fun p hp => ?_
      rw [hsum D p, hsum D' p]
      exact sum_lam_pow D D' p hp
    have hsqrt : ∀ (E : SchmidtDecomp psi),
        Multiset.map Real.sqrt (Multiset.map (· ^ 2) E.coeffs) = E.coeffs := by
      intro E
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id _)
      intro x hx
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
      simpa using Real.sqrt_sq (E.lam_pos k).le
    rw [← hsqrt D, ← hsqrt D', key]

end QI

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

