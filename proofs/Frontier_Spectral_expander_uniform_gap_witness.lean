import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Matrix

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- Flip the `i`-th coordinate of a vertex of the `k`-dimensional hypercube. -/
def flipAt {k : ℕ} (i : Fin k) (x : Fin k → Bool) : Fin k → Bool :=
  Function.update x i (!x i)

@[simp] lemma flipAt_self {k : ℕ} (i : Fin k) (x : Fin k → Bool) :
    flipAt i x i = !x i := by simp [flipAt]

lemma flipAt_of_ne {k : ℕ} {i j : Fin k} (h : j ≠ i) (x : Fin k → Bool) :
    flipAt i x j = x j := by simp [flipAt, h]

@[simp] lemma flipAt_flipAt {k : ℕ} (i : Fin k) (x : Fin k → Bool) :
    flipAt i (flipAt i x) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [flipAt_of_ne h]

lemma flipAt_ne {k : ℕ} (i : Fin k) (x : Fin k → Bool) : flipAt i x ≠ x := by
  intro h
  have := congrArg (fun y => y i) h
  simp at this

lemma flipAt_injective_index {k : ℕ} (x : Fin k → Bool) :
    Function.Injective (fun i : Fin k => flipAt i x) := by
  intro i j h
  by_contra hij
  have h1 := congrArg (fun y => y i) h
  simp only [flipAt_self, flipAt_of_ne hij] at h1
  exact (Bool.not_ne_self (x i)) h1

/-- The `k`-dimensional hypercube graph `Q k`: vertices are bit strings of length `k`,
with an edge between strings differing in exactly one coordinate. -/
def hypercube (k : ℕ) : SimpleGraph (Fin k → Bool) where
  Adj x y := ∃ i, y = flipAt i x
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by simp⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi⟩ := h
    exact flipAt_ne i x hi.symm⟩

instance hypercubeDecidableAdj (k : ℕ) : DecidableRel (hypercube k).Adj := fun x y =>
  inferInstanceAs (Decidable (∃ i, y = flipAt i x))

lemma hypercube_adj_iff {k : ℕ} {x y : Fin k → Bool} :
    (hypercube k).Adj x y ↔ ∃ i, y = flipAt i x := Iff.rfl

lemma hypercube_neighborFinset (k : ℕ) (x : Fin k → Bool) :
    (hypercube k).neighborFinset x = Finset.image (fun i : Fin k => flipAt i x) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube_adj_iff, eq_comm]

lemma hypercube_degree (k : ℕ) (x : Fin k → Bool) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, hypercube_neighborFinset,
    Finset.card_image_of_injective _ (flipAt_injective_index x), Finset.card_univ,
    Fintype.card_fin]

lemma sum_over_neighbors {k : ℕ} (v : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ∑ y ∈ (hypercube k).neighborFinset x, v y = ∑ i, v (flipAt i x) := by
  rw [hypercube_neighborFinset,
    Finset.sum_image (fun i _ j _ h => flipAt_injective_index x h)]

/-- The action of the graph Laplacian of the hypercube on a vector. -/
lemma lapMatrix_mulVec_apply {k : ℕ} (v : (Fin k → Bool) → ℝ) (x : Fin k → Bool) :
    ((hypercube k).lapMatrix ℝ *ᵥ v) x = k * v x - ∑ i, v (flipAt i x) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, hypercube_degree, sum_over_neighbors]

/-! ## The Dirichlet energy and the Poincaré inequality -/

/-- The Dirichlet energy `∑_x ∑_i (f x - f (flip i x))²` of `f` on the hypercube. -/
def energy (k : ℕ) (f : (Fin k → Bool) → ℝ) : ℝ :=
  ∑ x, ∑ i, (f x - f (flipAt i x)) ^ 2

lemma sum_cons_split {k : ℕ} (F : (Fin (k + 1) → Bool) → ℝ) :
    ∑ x, F x = ∑ y : Fin k → Bool, (F (Fin.cons true y) + F (Fin.cons false y)) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Bool))
      (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl), Fintype.sum_prod_type]
  simp [Finset.sum_add_distrib]

@[simp] lemma flipAt_zero_cons {k : ℕ} (b : Bool) (y : Fin k → Bool) :
    flipAt 0 (Fin.cons b y) = Fin.cons (!b) y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [flipAt]
  · intro i
    simp [flipAt_of_ne (Fin.succ_ne_zero i)]

@[simp] lemma flipAt_succ_cons {k : ℕ} (i : Fin k) (b : Bool) (y : Fin k → Bool) :
    flipAt i.succ (Fin.cons b y) = Fin.cons b (flipAt i y) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [flipAt_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · intro j'
    by_cases h : j' = i
    · subst h; simp [flipAt]
    · simp [flipAt_of_ne (fun hh => h (Fin.succ_injective _ hh)), flipAt_of_ne h]

lemma energy_succ {k : ℕ} (f : (Fin (k + 1) → Bool) → ℝ) :
    energy (k + 1) f =
      2 * (∑ y : Fin k → Bool, (f (Fin.cons true y) - f (Fin.cons false y)) ^ 2)
        + energy k (fun y => f (Fin.cons true y)) + energy k (fun y => f (Fin.cons false y)) := by
  rw [energy, sum_cons_split, energy, energy, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Fin.sum_univ_succ, flipAt_zero_cons, flipAt_succ_cons, Bool.not_true, Bool.not_false]
  ring

/-- The Poincaré inequality for the hypercube: `2^k` times the Dirichlet energy dominates
`4` times the (unnormalized) variance. -/
lemma poincare (k : ℕ) (f : (Fin k → Bool) → ℝ) :
    4 * ((2 ^ k : ℝ) * (∑ x, (f x) ^ 2) - (∑ x, f x) ^ 2) ≤ (2 ^ k : ℝ) * energy k f := by
  induction k with
  | zero => simp [energy]
  | succ k ih =>
    set g : (Fin k → Bool) → ℝ := fun y => f (Fin.cons true y) with hg
    set h : (Fin k → Bool) → ℝ := fun y => f (Fin.cons false y) with hh
    have hsum : ∑ x, f x = (∑ y, g y) + ∑ y, h y := by
      rw [sum_cons_split f, Finset.sum_add_distrib]
    have hsq : ∑ x, (f x) ^ 2 = (∑ y, (g y) ^ 2) + ∑ y, (h y) ^ 2 := by
      rw [sum_cons_split (fun x => (f x) ^ 2), Finset.sum_add_distrib]
    have hE := energy_succ f
    have hCS : ((∑ y, g y) - ∑ y, h y) ^ 2 ≤ (2 ^ k : ℝ) * ∑ y, (g y - h y) ^ 2 := by
      have hcard : ((Finset.univ : Finset (Fin k → Bool)).card : ℝ) = (2 ^ k : ℝ) := by
        simp [Finset.card_univ]
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k → Bool)))
        (f := fun y => g y - h y)
      rwa [Finset.sum_sub_distrib, hcard] at this
    have ihg := ih g
    have ihh := ih h
    have e1 : ((∑ y, g y) + ∑ y, h y) ^ 2
        = (∑ y, g y) ^ 2 + 2 * (∑ y, g y) * (∑ y, h y) + (∑ y, h y) ^ 2 := by ring
    have e2 : ((∑ y, g y) - ∑ y, h y) ^ 2
        = (∑ y, g y) ^ 2 - 2 * (∑ y, g y) * (∑ y, h y) + (∑ y, h y) ^ 2 := by ring
    have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hsq, hsum, hE, e1, hpow]
    nlinarith [ihg, ihh, hCS, e2]

/-! ## Quadratic form identity -/

lemma sum_flip_comp {k : ℕ} (i : Fin k) (F : (Fin k → Bool) → ℝ) :
    ∑ x, F (flipAt i x) = ∑ x, F x :=
  Fintype.sum_equiv (Function.Involutive.toPerm (flipAt i) (fun x => flipAt_flipAt i x)) _ _
    (fun _ => rfl)

lemma energy_eq_two_mul_quadratic {k : ℕ} (v : (Fin k → Bool) → ℝ) :
    energy k v = 2 * ∑ x, v x * ((hypercube k).lapMatrix ℝ *ᵥ v) x := by
  have key : ∑ x, ∑ i, ((v (flipAt i x)) ^ 2 - (v x) ^ 2) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_sub_distrib, sum_flip_comp i (fun x => (v x) ^ 2), sub_self]
  have expand : energy k v
      = 2 * (∑ x, ∑ i, ((v x) ^ 2 - v x * v (flipAt i x)))
        + ∑ x, ∑ i, ((v (flipAt i x)) ^ 2 - (v x) ^ 2) := by
    rw [energy, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [expand, key, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lapMatrix_mulVec_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.mul_sum, nsmul_eq_mul]
  ring

/-! ## Main theorem -/

lemma two_is_eigenvalue (k : ℕ) (hk : 1 ≤ k) :
    ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = (2 : ℝ) • v := by
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  refine ⟨fun x => if x i0 then -1 else 1, ?_, ?_⟩
  · intro hcon
    have := congrFun hcon (fun _ => false)
    norm_num at this
  · funext x
    set v : (Fin k → Bool) → ℝ := fun x => if x i0 then -1 else 1 with hv
    have hflip0 : v (flipAt i0 x) = - v x := by
      simp only [hv, flipAt_self]
      cases hx : x i0 <;> norm_num
    have hflipne : ∀ i : Fin k, i ≠ i0 → v (flipAt i x) = v x := by
      intro i hi
      simp only [hv, flipAt_of_ne (Ne.symm hi)]
    have hterm : ∀ i : Fin k, v (flipAt i x) = v x - (if i = i0 then 2 * v x else 0) := by
      intro i
      by_cases hi : i = i0
      · subst hi; rw [hflip0, if_pos rfl]; ring
      · rw [hflipne i hi]; simp [hi]
    rw [lapMatrix_mulVec_apply]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq' Finset.univ i0 (fun _ => 2 * v x)]
    simp only [Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    ring

lemma eigenvalue_lower_bound {k : ℕ} {μ : ℝ} (hμ : μ ≠ 0) {v : (Fin k → Bool) → ℝ}
    (hv : v ≠ 0) (hL : (hypercube k).lapMatrix ℝ *ᵥ v = μ • v) : 2 ≤ μ := by
  -- the eigenvector for a nonzero eigenvalue has zero mean
  have hrowsum : ∑ x, ((hypercube k).lapMatrix ℝ *ᵥ v) x = 0 := by
    have : ∀ x, ((hypercube k).lapMatrix ℝ *ᵥ v) x = (k : ℝ) * v x - ∑ i, v (flipAt i x) := by
      intro x; exact lapMatrix_mulVec_apply v x
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
    have : ∑ i : Fin k, ∑ x, v (flipAt i x) = ∑ _i : Fin k, ∑ x, v x :=
      Finset.sum_congr rfl (fun i _ => sum_flip_comp i v)
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]
  have hmean : ∑ x, v x = 0 := by
    have h1 : ∑ x, ((hypercube k).lapMatrix ℝ *ᵥ v) x = μ * ∑ x, v x := by
      rw [hL]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hrowsum] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd h hμ
    · exact h
  have hQpos : 0 < ∑ x, (v x) ^ 2 := by
    obtain ⟨x0, hx0⟩ : ∃ x, v x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hv (funext fun x => hcon x)
    refine Finset.sum_pos' (fun x _ => sq_nonneg (v x)) ⟨x0, Finset.mem_univ x0, ?_⟩
    exact pow_pos (abs_pos.mpr hx0) 2 |>.trans_le (le_of_eq (sq_abs (v x0)))
  have henergy : energy k v = 2 * μ * ∑ x, (v x) ^ 2 := by
    rw [energy_eq_two_mul_quadratic v, hL]
    have : ∀ x, v x * ((μ • v) x) = μ * (v x) ^ 2 := by
      intro x; simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum]
    ring
  have hpc := poincare k v
  rw [hmean, henergy] at hpc
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [hpc, mul_pos hpow hQpos]

/-- **Uniform spectral gap of the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` on `2 ^ k` vertices equals `2`; in particular the family `(Q k)` has a spectral gap
bounded below by `2`, uniformly in `k`. -/
theorem expander_uniform_gap_witness (k : ℕ) (hk : 1 ≤ k) :
    IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
      (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} 2 := by
  constructor
  · exact ⟨two_ne_zero, two_is_eigenvalue k hk⟩
  · rintro μ ⟨hμ, v, hv, hL⟩
    exact eigenvalue_lower_bound hμ hv hL

/-- The hypercube `Q k` has `2 ^ k` vertices. -/
lemma hypercube_card_vertices (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by simp

/-- **Existence of a uniform spectral gap.** A single positive constant (namely `2`), independent
of `k`, is the smallest nonzero Laplacian eigenvalue of every hypercube `Q k` with `k ≥ 1`. -/
theorem hypercube_uniform_spectral_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      IsLeast {μ : ℝ | μ ≠ 0 ∧ ∃ v : (Fin k → Bool) → ℝ, v ≠ 0 ∧
        (hypercube k).lapMatrix ℝ *ᵥ v = μ • v} c :=
  ⟨2, two_pos, expander_uniform_gap_witness⟩

end Frontier.Spectral

