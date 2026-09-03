/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

namespace Frontier

variable {n : ℕ}

/-! ## The hypercube and coordinate flips -/

/-- `cflip x i` is the hypercube vertex obtained from `x` by flipping the `i`-th coordinate. -/
def cflip (x : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update x i (!x i)

@[simp] lemma cflip_apply_self (x : Fin n → Bool) (i : Fin n) : cflip x i i = !x i := by
  simp [cflip]

lemma cflip_apply_of_ne (x : Fin n → Bool) {i j : Fin n} (h : j ≠ i) : cflip x i j = x j := by
  simp [cflip, Function.update_of_ne h]

@[simp] lemma cflip_cflip (x : Fin n → Bool) (i : Fin n) : cflip (cflip x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [cflip_apply_of_ne _ h, cflip_apply_of_ne _ h]

lemma cflip_ne (x : Fin n → Bool) (i : Fin n) : cflip x i ≠ x := by
  intro h
  have := congrArg (fun y => y i) h
  simp at this

lemma cflip_comm (x : Fin n → Bool) (i j : Fin n) :
    cflip (cflip x i) j = cflip (cflip x j) i := by
  funext k
  by_cases hki : k = i
  · subst hki
    by_cases hkj : k = j
    · subst hkj; rfl
    · rw [cflip_apply_of_ne _ hkj, cflip_apply_self, cflip_apply_self,
        cflip_apply_of_ne _ hkj]
  · by_cases hkj : k = j
    · subst hkj
      rw [cflip_apply_self, cflip_apply_of_ne _ hki, cflip_apply_of_ne _ hki,
        cflip_apply_self]
    · rw [cflip_apply_of_ne _ hkj, cflip_apply_of_ne _ hki, cflip_apply_of_ne _ hki,
        cflip_apply_of_ne _ hkj]

lemma cflip_injective (x : Fin n → Bool) : Function.Injective (cflip x) := by
  intro i j h
  by_contra hne
  have h1 : cflip x i i = cflip x j i := by rw [h]
  rw [cflip_apply_self, cflip_apply_of_ne _ hne] at h1
  simp at h1

/-! ## Toggling a coordinate inside a filtered cardinality -/

/-- If `i` is not in `s`, filtering `s` by `cflip x i` gives the same set as filtering by `x`. -/
lemma filter_cflip_of_not_mem {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) (x : Fin n → Bool) :
    (s.filter (fun j => cflip x i j = true)) = (s.filter (fun j => x j = true)) := by
  apply Finset.filter_congr
  intro j hj
  have : j ≠ i := by rintro rfl; exact hi hj
  simp [cflip_apply_of_ne _ this]

/-- If `i ∈ s`, toggling coordinate `i` changes the number of `true` coordinates in `s` by one. -/
lemma card_filter_cflip_disj {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) (x : Fin n → Bool) :
    (s.filter (fun j => cflip x i j = true)).card + 1 = (s.filter (fun j => x j = true)).card ∨
      (s.filter (fun j => x j = true)).card + 1
        = (s.filter (fun j => cflip x i j = true)).card := by
  by_cases hx : x i = true
  · -- the true-set shrinks by one
    have hmem : i ∈ s.filter (fun j => x j = true) := by simp [hi, hx]
    have hset : (s.filter (fun j => cflip x i j = true))
        = (s.filter (fun j => x j = true)).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hjs, hj⟩
        have hji : j ≠ i := by
          rintro rfl
          rw [cflip_apply_self, hx] at hj
          simp at hj
        exact ⟨hji, hjs, by rwa [cflip_apply_of_ne _ hji] at hj⟩
      · rintro ⟨hji, hjs, hj⟩
        exact ⟨hjs, by rwa [cflip_apply_of_ne _ hji]⟩
    left
    rw [hset, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ (s.filter (fun j => x j = true)).card := Finset.card_pos.2 ⟨i, hmem⟩
    omega
  · -- the true-set grows by one
    have hnm : i ∉ s.filter (fun j => x j = true) := by simp [hx]
    have hset : (s.filter (fun j => cflip x i j = true))
        = insert i (s.filter (fun j => x j = true)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hjs, hj⟩
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr ⟨hjs, by rwa [cflip_apply_of_ne _ hji] at hj⟩
      · rintro (rfl | ⟨hjs, hj⟩)
        · refine ⟨hi, ?_⟩
          rw [cflip_apply_self]
          simp at hx
          simp [hx]
        · have hji : j ≠ i := by rintro rfl; rw [hj] at hx; simp at hx
          exact ⟨hjs, by rwa [cflip_apply_of_ne _ hji]⟩
    right
    rw [hset, Finset.card_insert_of_notMem hnm]

/-- If `i ∈ s`, toggling coordinate `i` flips the parity of the number of `true` coordinates
in `s`. -/
lemma neg_one_pow_filter_cflip {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) (x : Fin n → Bool) :
    ((-1 : ℝ)) ^ ((s.filter (fun j => cflip x i j = true)).card)
      = -((-1 : ℝ)) ^ ((s.filter (fun j => x j = true)).card) := by
  rcases card_filter_cflip_disj hi x with h | h
  · rw [← h, pow_succ]
    ring
  · rw [← h, pow_succ]
    ring

/-! ## The Huang sign matrix, as an operator -/

/-- The sign attached to the hypercube edge `{x, cflip x i}`: `(-1)` to the number of `true`
coordinates of `x` strictly before `i`. This is the signing of the hypercube used by Huang. -/
def hsign (x : Fin n → Bool) (i : Fin n) : ℝ :=
  (-1 : ℝ) ^ (((Finset.Iio i).filter (fun j => x j = true)).card)

lemma hsign_mul_self (x : Fin n → Bool) (i : Fin n) : hsign x i * hsign x i = 1 := by
  unfold hsign
  rw [← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

lemma hsign_flip_of_le {i j : Fin n} (h : j ≤ i) (x : Fin n → Bool) :
    hsign (cflip x i) j = hsign x j := by
  unfold hsign
  rw [filter_cflip_of_not_mem (by simp; omega) x]

lemma hsign_flip_of_lt {i j : Fin n} (h : i < j) (x : Fin n → Bool) :
    hsign (cflip x i) j = - hsign x j := by
  unfold hsign
  rw [neg_one_pow_filter_cflip (by simpa using h) x]

/-- The two-step sign contributions along the two paths of a square cancel. -/
lemma hsign_square_cancel (x : Fin n → Bool) {i j : Fin n} (h : i ≠ j) :
    hsign x i * hsign (cflip x i) j + hsign x j * hsign (cflip x j) i = 0 := by
  rcases lt_or_gt_of_ne h with hij | hij
  · rw [hsign_flip_of_lt hij x, hsign_flip_of_le (le_of_lt hij) x]
    ring
  · rw [hsign_flip_of_lt hij x, hsign_flip_of_le (le_of_lt hij) x]
    ring

lemma abs_hsign (x : Fin n → Bool) (i : Fin n) : |hsign x i| = 1 := by
  unfold hsign
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- Huang's signed adjacency operator on real functions on the hypercube. -/
def huangOp (n : ℕ) : ((Fin n → Bool) → ℝ) →ₗ[ℝ] ((Fin n → Bool) → ℝ) where
  toFun v := fun x => ∑ i : Fin n, hsign x i * v (cflip x i)
  map_add' u v := by
    funext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext x
    simp [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma huangOp_apply (v : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    huangOp n v x = ∑ i : Fin n, hsign x i * v (cflip x i) := rfl

/-- The defining property of Huang's matrix: its square is `n` times the identity. -/
lemma huangOp_huangOp (v : (Fin n → Bool) → ℝ) :
    huangOp n (huangOp n v) = (n : ℝ) • v := by
  funext x
  set F : Fin n → Fin n → ℝ :=
    fun i j => hsign x i * (hsign (cflip x i) j * v (cflip (cflip x i) j)) with hF
  have hexp : huangOp n (huangOp n v) x = ∑ i : Fin n, ∑ j : Fin n, F i j := by
    rw [huangOp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [huangOp_apply, Finset.mul_sum]
  have hsym : ∀ i j : Fin n, F i j + F j i = if i = j then 2 * v x else 0 := by
    intro i j
    have e1 : F i j = hsign x i * (hsign (cflip x i) j * v (cflip (cflip x i) j)) := rfl
    have e2 : F j i = hsign x j * (hsign (cflip x j) i * v (cflip (cflip x j) i)) := rfl
    rw [e1, e2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hsign_flip_of_le (le_refl i) x, cflip_cflip]
      linear_combination (2 * v x) * hsign_mul_self x i
    · rw [if_neg hij, cflip_comm x j i]
      linear_combination (v (cflip (cflip x i) j)) * hsign_square_cancel x hij
  have hswap : (∑ i : Fin n, ∑ j : Fin n, F j i) = ∑ i : Fin n, ∑ j : Fin n, F i j :=
    Finset.sum_comm
  have hdouble : (2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, F i j)
      = ∑ i : Fin n, ∑ j : Fin n, (F i j + F j i) := by
    have : ∑ i : Fin n, ∑ j : Fin n, (F i j + F j i)
        = (∑ i : Fin n, ∑ j : Fin n, F i j) + (∑ i : Fin n, ∑ j : Fin n, F j i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]
    rw [this, hswap]
    ring
  have hcount : (∑ i : Fin n, ∑ j : Fin n, (F i j + F j i)) = (n : ℝ) * (2 * v x) := by
    have : ∀ i : Fin n, (∑ j : Fin n, (F i j + F j i)) = 2 * v x := by
      intro i
      rw [Finset.sum_congr rfl fun j _ => hsym i j]
      simp
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [mul_comm]
  have : (2 : ℝ) * (huangOp n (huangOp n v) x) = 2 * ((n : ℝ) * v x) := by
    rw [hexp, hdouble, hcount]; ring
  have h2 : huangOp n (huangOp n v) x = (n : ℝ) * v x := by linarith
  simpa using h2

/-! ## Eigenspaces of the Huang operator -/

lemma mem_ker_iff (r : ℝ) (v : (Fin n → Bool) → ℝ) :
    v ∈ LinearMap.ker (huangOp n - r • LinearMap.id) ↔ huangOp n v = r • v := by
  simp [LinearMap.mem_ker, sub_eq_zero]

/-- The parity sign of a hypercube vertex. -/
def parSign (x : Fin n → Bool) : ℝ :=
  (-1 : ℝ) ^ ((Finset.univ.filter (fun j => x j = true)).card)

lemma parSign_mul_self (x : Fin n → Bool) : parSign x * parSign x = 1 := by
  unfold parSign
  rw [← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

lemma parSign_cflip (x : Fin n → Bool) (i : Fin n) : parSign (cflip x i) = - parSign x := by
  unfold parSign
  exact neg_one_pow_filter_cflip (Finset.mem_univ i) x

/-- Conjugation by the parity sign: an involutive linear automorphism of functions on the cube. -/
def parEquiv (n : ℕ) : ((Fin n → Bool) → ℝ) ≃ₗ[ℝ] ((Fin n → Bool) → ℝ) where
  toFun v := fun x => parSign x * v x
  map_add' u v := by funext x; simp [mul_add]
  map_smul' c v := by funext x; simp; ring
  invFun v := fun x => parSign x * v x
  left_inv v := by
    funext x
    simp only [← mul_assoc, parSign_mul_self, one_mul]
  right_inv v := by
    funext x
    simp only [← mul_assoc, parSign_mul_self, one_mul]

lemma parEquiv_apply (v : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    parEquiv n v x = parSign x * v x := rfl

/-- The parity conjugation anticommutes with the Huang operator. -/
lemma huangOp_parEquiv (v : (Fin n → Bool) → ℝ) :
    huangOp n (parEquiv n v) = - parEquiv n (huangOp n v) := by
  funext x
  rw [huangOp_apply]
  simp only [Pi.neg_apply, parEquiv_apply, huangOp_apply]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [parSign_cflip]
  ring

/-- The `+√n` eigenspace of the Huang operator. -/
noncomputable def huangPlus (n : ℕ) : Submodule ℝ ((Fin n → Bool) → ℝ) :=
  LinearMap.ker (huangOp n - (Real.sqrt n) • LinearMap.id)

/-- The `-√n` eigenspace of the Huang operator. -/
noncomputable def huangMinus (n : ℕ) : Submodule ℝ ((Fin n → Bool) → ℝ) :=
  LinearMap.ker (huangOp n + (Real.sqrt n) • LinearMap.id)

lemma mem_huangPlus {v : (Fin n → Bool) → ℝ} :
    v ∈ huangPlus n ↔ huangOp n v = (Real.sqrt n) • v := by
  simp [huangPlus, LinearMap.mem_ker, sub_eq_zero]

lemma mem_huangMinus {v : (Fin n → Bool) → ℝ} :
    v ∈ huangMinus n ↔ huangOp n v = (-(Real.sqrt n)) • v := by
  simp only [huangMinus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, neg_smul, eq_neg_iff_add_eq_zero]

lemma sq_sqrt_nat (n : ℕ) : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
  Real.mul_self_sqrt (by positivity)

lemma sqrt_nat_pos {n : ℕ} (hn : 0 < n) : 0 < Real.sqrt n :=
  Real.sqrt_pos.2 (by exact_mod_cast hn)

lemma huang_sup_eq_top {n : ℕ} (hn : 0 < n) : huangPlus n ⊔ huangMinus n = ⊤ := by
  set r : ℝ := Real.sqrt n with hrdef
  have hr : 0 < r := sqrt_nat_pos hn
  have hr2 : r * r = (n : ℝ) := sq_sqrt_nat n
  refine eq_top_iff.2 ?_
  intro v _
  rw [Submodule.mem_sup]
  refine ⟨(1 / (2 * r)) • (huangOp n v + r • v), ?_,
    (1 / (2 * r)) • (r • v - huangOp n v), ?_, ?_⟩
  · rw [mem_huangPlus]
    rw [map_smul, map_add, map_smul, huangOp_huangOp]
    funext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h2r : (2 : ℝ) * r ≠ 0 := by positivity
    field_simp
    linear_combination (-(v x)) * hr2
  · rw [mem_huangMinus]
    rw [map_smul, map_sub, map_smul, huangOp_huangOp]
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h2r : (2 : ℝ) * r ≠ 0 := by positivity
    field_simp
    linear_combination (v x) * hr2
  · funext x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h2r : (2 : ℝ) * r ≠ 0 := by positivity
    field_simp
    ring

lemma huang_inf_eq_bot {n : ℕ} (hn : 0 < n) : huangPlus n ⊓ huangMinus n = ⊥ := by
  have hr : 0 < Real.sqrt n := sqrt_nat_pos hn
  refine eq_bot_iff.2 ?_
  intro v hv
  simp only [Submodule.mem_inf] at hv
  obtain ⟨hp, hm⟩ := hv
  rw [mem_huangPlus] at hp
  rw [mem_huangMinus] at hm
  have : (Real.sqrt n) • v = (-(Real.sqrt n)) • v := by rw [← hp, hm]
  have hv : v = 0 := by
    funext x
    have := congrArg (fun w => w x) this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h0 : (2 * Real.sqrt n) * v x = 0 := by linarith
    have : Real.sqrt n ≠ 0 := ne_of_gt hr
    simpa [this] using (mul_eq_zero.1 h0)
  simp [hv]

lemma huang_map_parEquiv {n : ℕ} :
    Submodule.map (parEquiv n : ((Fin n → Bool) → ℝ) →ₗ[ℝ] ((Fin n → Bool) → ℝ))
      (huangPlus n) = huangMinus n := by
  have himg : ∀ v : (Fin n → Bool) → ℝ, v ∈ huangPlus n → parEquiv n v ∈ huangMinus n := by
    intro v hv
    rw [mem_huangPlus] at hv
    rw [mem_huangMinus, huangOp_parEquiv, hv, map_smul]
    funext x
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hpre : ∀ w : (Fin n → Bool) → ℝ, w ∈ huangMinus n → parEquiv n w ∈ huangPlus n := by
    intro w hw
    rw [mem_huangMinus] at hw
    rw [mem_huangPlus, huangOp_parEquiv, hw, map_smul]
    funext x
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  apply le_antisymm
  · rintro w hw
    simp only [Submodule.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact himg v hv
  · intro w hw
    refine ⟨parEquiv n w, hpre w hw, ?_⟩
    exact (parEquiv n).left_inv w

lemma finrank_cube (n : ℕ) : Module.finrank ℝ ((Fin n → Bool) → ℝ) = 2 ^ n := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

/-- The `+√n` eigenspace of the Huang operator has dimension exactly `2^(n-1)`. -/
lemma finrank_huangPlus {n : ℕ} (hn : 0 < n) :
    2 * Module.finrank ℝ (huangPlus n) = 2 ^ n := by
  have hmap : Module.finrank ℝ (huangMinus n) = Module.finrank ℝ (huangPlus n) := by
    rw [← huang_map_parEquiv]
    exact LinearEquiv.finrank_map_eq (parEquiv n) (huangPlus n)
  have key := Submodule.finrank_sup_add_finrank_inf_eq (huangPlus n) (huangMinus n)
  rw [huang_sup_eq_top hn, huang_inf_eq_bot hn, hmap] at key
  rw [finrank_top ℝ ((Fin n → Bool) → ℝ), finrank_bot ℝ ((Fin n → Bool) → ℝ),
    finrank_cube] at key
  omega

/-! ## From an eigenvector to a vertex of large degree -/

/-- If a nonzero `+√n`-eigenvector of the Huang operator is supported inside `S`, then some
vertex of `S` has at least `√n` neighbours inside `S`. -/
lemma exists_large_degree_of_eigenvector {n : ℕ} (S : Finset (Fin n → Bool))
    (v : (Fin n → Bool) → ℝ) (hv : huangOp n v = (Real.sqrt n) • v) (hv0 : v ≠ 0)
    (hsupp : ∀ x : Fin n → Bool, x ∉ S → v x = 0) :
    ∃ x ∈ S, Real.sqrt n ≤ ((Finset.univ.filter (fun i : Fin n => cflip x i ∈ S)).card : ℝ) := by
  obtain ⟨x0, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n → Bool)) (fun x => |v x|)
      ⟨fun _ => false, Finset.mem_univ _⟩
  have hne : ∃ y, v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  obtain ⟨y, hy⟩ := hne
  have hpos : 0 < |v x0| := lt_of_lt_of_le (abs_pos.2 hy) (hmax y (Finset.mem_univ _))
  have hx0S : x0 ∈ S := by
    by_contra h
    rw [hsupp x0 h] at hpos
    simp at hpos
  refine ⟨x0, hx0S, ?_⟩
  set D := Finset.univ.filter (fun i : Fin n => cflip x0 i ∈ S) with hD
  have hkey : Real.sqrt n * |v x0| ≤ (D.card : ℝ) * |v x0| := by
    have e1 : Real.sqrt n * |v x0| = |huangOp n v x0| := by
      have : huangOp n v x0 = Real.sqrt n * v x0 := by
        rw [hv]; simp
      rw [this, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have e2 : |huangOp n v x0| ≤ ∑ i : Fin n, |v (cflip x0 i)| := by
      rw [huangOp_apply]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_hsign, one_mul]
    have e3 : (∑ i : Fin n, |v (cflip x0 i)|) ≤ (D.card : ℝ) * |v x0| := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
        (fun i => cflip x0 i ∈ S) (fun i => |v (cflip x0 i)|)]
      have hzero : (∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (cflip x0 i ∈ S)),
          |v (cflip x0 i)|) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_filter] at hi
        rw [hsupp _ hi.2]
        simp
      rw [hzero, add_zero]
      calc (∑ i ∈ D, |v (cflip x0 i)|) ≤ ∑ _i ∈ D, |v x0| :=
            Finset.sum_le_sum fun i _ => hmax _ (Finset.mem_univ _)
        _ = (D.card : ℝ) * |v x0| := by rw [Finset.sum_const, nsmul_eq_mul]
    linarith [e1 ▸ le_trans e2 e3]
  exact le_of_mul_le_mul_right (by linarith) hpos

/-! ## Existence of an eigenvector supported in a large set -/

/-- If `S` occupies more than half of the hypercube, the `+√n` eigenspace of the Huang operator
contains a nonzero vector supported inside `S`. -/
lemma exists_eigenvector_supported {n : ℕ} (hn : 0 < n) (S : Finset (Fin n → Bool))
    (hS : 2 ^ n < 2 * S.card) :
    ∃ v : (Fin n → Bool) → ℝ, huangOp n v = (Real.sqrt n) • v ∧ v ≠ 0 ∧
      (∀ x : Fin n → Bool, x ∉ S → v x = 0) := by
  classical
  set res : ((Fin n → Bool) → ℝ) →ₗ[ℝ] ({x : Fin n → Bool // x ∉ S} → ℝ) :=
    LinearMap.funLeft ℝ ℝ (fun y : {x : Fin n → Bool // x ∉ S} => (y : Fin n → Bool)) with hres
  set phi : (huangPlus n) →ₗ[ℝ] ({x : Fin n → Bool // x ∉ S} → ℝ) :=
    res.comp (huangPlus n).subtype with hphi
  have hcard : Fintype.card {x : Fin n → Bool // x ∉ S} = 2 ^ n - S.card := by
    rw [Fintype.card_subtype_compl (fun x : Fin n → Bool => x ∈ S)]
    simp
  have hcodim : Module.finrank ℝ ({x : Fin n → Bool // x ∉ S} → ℝ) = 2 ^ n - S.card := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  have hrk := LinearMap.finrank_range_add_finrank_ker phi
  have hle : Module.finrank ℝ (LinearMap.range phi) ≤ 2 ^ n - S.card := by
    rw [← hcodim]
    exact Submodule.finrank_le _
  have hSle : S.card ≤ 2 ^ n := by
    have := Finset.card_le_univ S
    simpa using this
  have hdim := finrank_huangPlus (n := n) hn
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker phi) := by omega
  have : Nontrivial (LinearMap.ker phi) := Module.finrank_pos_iff.1 hpos
  obtain ⟨w, hw⟩ := exists_ne (0 : LinearMap.ker phi)
  refine ⟨((w : (huangPlus n)) : (Fin n → Bool) → ℝ), ?_, ?_, ?_⟩
  · exact mem_huangPlus.1 (w : (huangPlus n)).2
  · intro hzero
    apply hw
    apply Subtype.ext
    apply Subtype.ext
    exact hzero
  · intro x hx
    have hker : phi (w : (huangPlus n)) = 0 := w.2
    have h2 : phi (w : (huangPlus n)) (⟨x, hx⟩ : {x : Fin n → Bool // x ∉ S}) = 0 := by
      rw [hker]; rfl
    exact h2

/-! ## Huang's theorem -/

/--
**Huang's sensitivity theorem** (combinatorial core, Huang 2019).

If a set `S` of vertices of the `n`-dimensional Boolean hypercube `{0,1}^n` contains more than
half of all vertices (`2^n < 2 * |S|`), then some vertex of `S` has at least `√n` neighbours
inside `S`; that is, the induced subgraph on `S` has maximum degree at least `√n`.

This is the statement that, via the Gotsman-Linial equivalence, shows that the sensitivity and
the degree of a Boolean function are polynomially related.
-/
theorem huang_sensitivity {n : ℕ} (S : Finset (Fin n → Bool)) (hS : 2 ^ n < 2 * S.card) :
    ∃ x ∈ S, Real.sqrt n ≤ ((Finset.univ.filter (fun i : Fin n => cflip x i ∈ S)).card : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hne : S.Nonempty := by
      rw [← Finset.card_pos]
      simp only [pow_zero] at hS
      omega
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, hx, ?_⟩
    simp
  · obtain ⟨v, hv, hv0, hsupp⟩ := exists_eigenvector_supported hn S hS
    exact exists_large_degree_of_eigenvector S v hv hv0 hsupp

/-! ## A consequence for the sensitivity of Boolean functions -/

/-- The (local) sensitivity of a Boolean function `f` at a point `x`: the number of coordinates
whose flip changes the value of `f`. -/
def sens (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => f (cflip x i) ≠ f x)).card

/-- The parity function on the hypercube. -/
def cpar (x : Fin n → Bool) : Bool :=
  (Finset.univ.filter (fun j => x j = true)).card % 2 == 1

lemma cpar_cflip (x : Fin n → Bool) (i : Fin n) : cpar (cflip x i) = !cpar x := by
  unfold cpar
  rcases card_filter_cflip_disj (Finset.mem_univ i) x with h | h
  · rw [← h]
    rcases Nat.even_or_odd (Finset.univ.filter (fun j => cflip x i j = true)).card with he | he
    · rw [Nat.even_iff] at he
      simp [he, Nat.add_mod]
    · rw [Nat.odd_iff] at he
      simp [he, Nat.add_mod]
  · rw [← h]
    rcases Nat.even_or_odd (Finset.univ.filter (fun j => x j = true)).card with he | he
    · rw [Nat.even_iff] at he
      simp [he, Nat.add_mod]
    · rw [Nat.odd_iff] at he
      simp [he, Nat.add_mod]

/--
**A sensitivity consequence of Huang's theorem.**

Let `f : {0,1}^n → {0,1}` be a Boolean function whose agreement set with the parity function
does not consist of exactly half of the hypercube. Then `f` has a point of sensitivity at
least `√n`.

This is the step by which Huang's hypercube theorem yields a `√d` lower bound on sensitivity for
functions of full degree `d`, hence the polynomial relation between sensitivity and degree.
-/
theorem huang_sensitivity_parity {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : 2 * (Finset.univ.filter (fun x : Fin n → Bool => f x = cpar x)).card ≠ 2 ^ n) :
    ∃ x : Fin n → Bool, Real.sqrt n ≤ (sens f x : ℝ) := by
  classical
  set A : Finset (Fin n → Bool) := Finset.univ.filter (fun x => f x = cpar x) with hA
  set B : Finset (Fin n → Bool) := Finset.univ.filter (fun x => ¬ (f x = cpar x)) with hB
  have htot : A.card + B.card = 2 ^ n := by
    rw [hA, hB, Finset.card_filter_add_card_filter_not]
    simp
  -- in either case the chosen set covers more than half of the cube
  have main : ∀ S : Finset (Fin n → Bool), 2 ^ n < 2 * S.card →
      (∀ y : Fin n → Bool, y ∈ S → ∀ z : Fin n → Bool, z ∈ S → (∀ i, z = cflip y i → f z ≠ f y)) →
      ∃ x : Fin n → Bool, Real.sqrt n ≤ (sens f x : ℝ) := by
    intro S hS hedge
    obtain ⟨x, hxS, hx⟩ := huang_sensitivity S hS
    refine ⟨x, le_trans hx ?_⟩
    have hsub : (Finset.univ.filter (fun i : Fin n => cflip x i ∈ S))
        ⊆ (Finset.univ.filter (fun i : Fin n => f (cflip x i) ≠ f x)) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ i, hedge x hxS (cflip x i) hi.2 i rfl⟩
    exact_mod_cast Nat.cast_le.2 (Finset.card_le_card hsub)
  rcases lt_trichotomy (2 * A.card) (2 ^ n) with hlt | heq | hgt
  · refine main B (by omega) ?_
    rintro y hy z hz i rfl
    rw [hB, Finset.mem_filter] at hy hz
    have h1 : f y = !cpar y := by
      cases hfy : f y <;> cases hcy : cpar y <;> simp_all
    have h2 : f (cflip y i) = !cpar (cflip y i) := by
      cases hfy : f (cflip y i) <;> cases hcy : cpar (cflip y i) <;> simp_all
    rw [h1, h2, cpar_cflip]
    simp
  · exact absurd heq hf
  · refine main A hgt ?_
    rintro y hy z hz i rfl
    rw [hA, Finset.mem_filter] at hy hz
    rw [hy.2, hz.2, cpar_cflip]
    simp

end Frontier

