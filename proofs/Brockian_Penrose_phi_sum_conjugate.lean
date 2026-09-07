/-
  Brockian/PenroseL2.lean — D₅ Penrose cut-and-project + L² operator theory.

  PORT of _ingest/repo_original/PenroseTiling.lean (Aristotle, ~Mathlib v4.24)
  to Mathlib v4.32.0. Namespace: `Brockian.Penrose`.

  DROPPED from the original (see report): the EuclideanSpace ℝ (Fin 2) geometry layer
  (toReal2, vertex, vertex_norm, Pentagon, rotate_vec, rotate, S, reflect, R,
  IsOrthogonal, R_orthogonal, S_orthogonal, rotate_eq_R_mulVec,
  pentagon_rotation_invariant, pentagon_reflection_invariant). These break under
  Mathlib's WithLp/`.ofLp` refactor of EuclideanSpace — a nontrivial API rework, not
  mechanical drift — and are outside the L² operator-theory core. The ℂ-valued
  `rotation_is_multiplication` (Golden Gate) and all cut-and-project / adjacency /
  L² operator theory are retained.

  Verification (spec §2A): AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Real Complex Finset Matrix MeasureTheory

namespace Brockian.Penrose

/-!
## Layer 1: Golden Ratio Algebra (Complete, no sorries)
-/

/-- The golden ratio phi = (1 + √5)/2 -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The golden conjugate phi_bar = (1 - √5)/2 -/
def phi_bar : ℝ := (1 - Real.sqrt 5) / 2

theorem sqrt5_gt_one : 1 < Real.sqrt 5 := by
  simpa using sqrt_lt_sqrt (by norm_num) (by norm_num : (1:ℝ) < 5)

theorem sqrt5_gt_two : 2 < Real.sqrt 5 := by
  rw [← sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  exact sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem phi_pos : 0 < phi := by
  unfold phi; have : 0 < Real.sqrt 5 := sqrt_pos.2 (by norm_num); linarith

theorem phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos

theorem phi_gt_one : 1 < phi := by unfold phi; linarith [sqrt5_gt_two]

/-- **FUNDAMENTAL EQUATION**: phi² = phi + 1 -/
theorem phi_squared : phi ^ 2 = phi + 1 := by
  unfold phi; field_simp; ring
  rw [sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; ring

theorem phi_equation    : phi ^ 2 - phi - 1 = 0 := by linarith [phi_squared]
theorem phi_reciprocal  : 1 / phi = phi - 1 := by
  have h := phi_squared; field_simp [phi_ne_zero] at h ⊢; linarith
theorem phi_sum_conjugate     : phi + phi_bar = 1     := by unfold phi phi_bar; field_simp; ring
theorem phi_product_conjugate : phi * phi_bar = -1    := by
  unfold phi phi_bar; field_simp; ring
  rw [sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; ring

/-!
## Layer 2: Complex Pentagon (Complete, no sorries)
-/

/-- Primitive 5th root of unity zeta5 = exp(2πi/5) -/
def zeta5 : ℂ := exp (2 * π * I / 5)

/-!
### FIX 3: zeta5^5 = 1

Use `Complex.exp_int_mul_two_pi_mul_I` (or equivalent) directly.
The computation: zeta5^5 = exp(5 · 2πi/5) = exp(2πi · 1) = 1.
We write this as exp(2πi · 1) via `Complex.exp_two_pi_mul_I`.
-/
theorem zeta5_pow_five : zeta5 ^ 5 = 1 := by
  -- By definition of $zeta5$, we know that $zeta5 = e^{2\pi i / 5}$.
  have hzeta5_def : zeta5 = Complex.exp (2 * Real.pi * Complex.I / 5) := by
    -- By definition of $zeta5$, we have $zeta5 = e^{2\pi i / 5}$.
    simp [zeta5];
  rw [ hzeta5_def, ← Complex.exp_nat_mul, mul_comm ] ; norm_num

theorem zeta5_norm : ‖zeta5‖ = 1 := by
  -- The norm of a complex exponential is 1 because $e^{i\theta}$ lies on the unit circle.
  simp [zeta5, Complex.norm_exp]

/-- k-th pentagon vertex: zeta5^k -/
def pentagonVertex (k : Fin 5) : ℂ := zeta5 ^ (k : ℕ)

theorem pentagonVertex_norm (k : Fin 5) : ‖pentagonVertex k‖ = 1 := by
  -- The norm of a complex number on the unit circle is 1.
  simp [pentagonVertex];
  -- The norm of $e^{2\pi i / 5}$ is 1 because it lies on the unit circle.
  simp [zeta5, Complex.norm_exp]


/-!
### The Golden Gate Theorem
-/

/-!
FIX 4: k=4 case — use `simpa [pow_succ, zeta5_pow_five]`, not `linarith`
(linarith is for ordered fields/reals, not ℂ).
-/
/-- **GOLDEN GATE**: pentagonVertex (k+1) = zeta5 · pentagonVertex k -/
theorem rotation_is_multiplication (k : Fin 5) :
    pentagonVertex (k + 1) = zeta5 * pentagonVertex k := by
      -- By definition of $pentagonVertex$, we have $pentagonVertex (k + 1) = e^{i \cdot 2\pi (k + 1) / 5}$.
      simp [pentagonVertex];
      fin_cases k <;> norm_num [ pow_succ', Fin.val_add ];
      -- By definition of $zeta5$, we know that $zeta5^5 = 1$.
      have h_zeta5_pow : zeta5 ^ 5 = 1 := by
        -- By definition of $zeta5$, we know that $zeta5 = e^{2\pi i / 5}$.
        have hzeta5_def : zeta5 = Complex.exp (2 * Real.pi * Complex.I / 5) := by
          -- By definition of $zeta5$, we have $zeta5 = e^{2\pi i / 5}$.
          simp [zeta5];
        rw [ hzeta5_def, ← Complex.exp_nat_mul, mul_comm ] ; norm_num;
      linear_combination' h_zeta5_pow.symm


/-!
## Layer 4: Cut-and-Project Construction
-/

/-- De Bruijn shift parameter for aperiodicity -/
def gamma : Fin 5 → ℝ := fun _ => 1 / (2 * Real.sqrt 5)

/-- Physical projection pi_para : ℤ⁵ → ℂ -/
def proj_para (n : Fin 5 → ℤ) : ℂ :=
  ∑ k, (n k : ℂ) * pentagonVertex k

/-- Internal projection pi_perp : ℤ⁵ → ℂ -/
def proj_perp (n : Fin 5 → ℤ) : ℂ :=
  ∑ k, (n k : ℂ) * pentagonVertex (2 * k)

/-- pi_perp for real coordinates -/
def proj_perp_real (v : Fin 5 → ℝ) : ℂ :=
  ∑ k, (v k : ℂ) * pentagonVertex (2 * k)

/-- Acceptance window: projection of unit hypercube -/
def Window : Set ℂ :=
  { z | ∃ v : Fin 5 → ℝ, (∀ k, 0 ≤ v k ∧ v k ≤ 1) ∧ z = proj_perp_real v }

/-- **PENROSE TILING**: Cut-and-project vertex set -/
def Vertices : Set ℂ :=
  { z | ∃ n : Fin 5 → ℤ, z = proj_para n ∧ (proj_perp n + proj_perp_real gamma) ∈ Window }

/-- Symmetric adjacency: u ~ v iff they differ by ±pentagonVertex k -/
def adjacent (u v : ℂ) : Prop :=
  ∃ k : Fin 5, v = u + pentagonVertex k ∨ v = u - pentagonVertex k

theorem adjacent_symm : ∀ u v : ℂ, adjacent u v → adjacent v u := by
  rintro u v ⟨k, hv | hv⟩
  · -- v = u + e  →  u = v - e
    exact ⟨k, Or.inr (by rw [hv]; ring)⟩
  · -- v = u - e  →  u = v + e
    exact ⟨k, Or.inl (by rw [hv]; ring)⟩

theorem adjacent_loopless : ∀ u : ℂ, ¬ adjacent u u := by
  -- By definition of adjacent, if u is adjacent to itself, then there exists some k such that u = u + pentagonVertex k or u = u - pentagonVertex k.
  intro u
  simp [adjacent];
  -- Since $zeta5$ is a primitive 5th root of unity, its powers are non-zero. Therefore, $pentagonVertex x$ is never zero.
  have h_pentagonVertex_ne_zero : ∀ x : Fin 5, pentagonVertex x ≠ 0 := by
    -- Since $zeta5$ is a primitive 5th root of unity, its powers are non-zero. Therefore, $pentagonVertex x$ is never zero for any $x$.
    intro x
    simp [pentagonVertex, zeta5];
  -- Since $pentagonVertex x$ is never zero, $u$ cannot equal $u - pentagonVertex x$.
  intros x
  exact ⟨h_pentagonVertex_ne_zero x, by
    -- Since $pentagonVertex x$ is non-zero, subtracting it from $u$ will result in a different value.
    have h_sub_ne : pentagonVertex x ≠ 0 := h_pentagonVertex_ne_zero x
    exact fun h => h_sub_ne (by linear_combination' h)⟩

/-- The Penrose tiling graph -/
def PenroseGraph : SimpleGraph Vertices where
  Adj u v := adjacent u.1 v.1
  symm := ⟨by intro u v h; exact adjacent_symm u.1 v.1 h⟩
  loopless := ⟨by intro u h; exact adjacent_loopless u.1 h⟩

/-- Potential neighbors: all ±pentagonVertex shifts of u -/
def potentialNeighbors (u : ℂ) : Set ℂ :=
  (Set.range fun k : Fin 5 => u + pentagonVertex k) ∪
  (Set.range fun k : Fin 5 => u - pentagonVertex k)

/-- Neighbors are within potentialNeighbors -/
lemma neighbor_subset (u : Vertices) :
    PenroseGraph.neighborSet u ⊆ { v | v.1 ∈ potentialNeighbors u.1 } := by
  intro v hv
  simp only [SimpleGraph.neighborSet, SimpleGraph.mem_neighborSet] at hv
  simp only [Set.mem_setOf_eq, potentialNeighbors, Set.mem_union,
             Set.mem_range]
  obtain ⟨k, hk | hk⟩ := hv
  · exact Or.inl ⟨k, hk.symm⟩
  · exact Or.inr ⟨k, hk.symm⟩

/-- Penrose vertices are countable -/
instance : Countable Vertices := by
  -- The set of integer vectors is countable.
  have h_int_vectors_countable : Set.Countable (Set.range (fun n : Fin 5 → ℤ => ∑ k, (n k : ℂ) * pentagonVertex k)) := by
    exact Set.countable_range _;
  refine' Set.Countable.mono _ ( h_int_vectors_countable.image _ );
  swap;
  exact fun x => x;
  intro x hx; obtain ⟨ n, hn ⟩ := hx; aesop;

/-- Counting measure on Penrose vertices -/
noncomputable def mu : Measure Vertices := Measure.count

noncomputable instance : MeasureSpace Vertices := ⟨mu⟩

/-- The ℓ² Hilbert space ℓ²(Vertices, ℂ) -/
abbrev L2 : Type := Lp ℂ 2 mu

noncomputable instance : NormedAddCommGroup L2 := Lp.instNormedAddCommGroup
noncomputable instance : NormedSpace ℂ L2 := Lp.instNormedSpace
noncomputable instance : CompleteSpace L2 := Lp.instCompleteSpace
/-- The inner product on L2 — inferred from the general Lp theory -/
noncomputable instance : InnerProductSpace ℂ L2 := by infer_instance

/-- ae-equality under counting measure ↔ pointwise equality -/
lemma ae_eq_of_count {f g : Vertices → ℂ} (h : f =ᵐ[mu] g) : f = g := by
  -- Since the measure is the counting measure, the almost everywhere condition implies that f and g are equal at every point. Hence, ∀ a, f a = g a.
  have h_eq : ∀ a : Vertices, f a = g a := by
    intro a;
    contrapose! h;
    refine' ne_of_gt ( lt_of_lt_of_le _ ( MeasureTheory.measure_mono _ ) );
    -- The measure of a singleton set in the counting measure is 1, which is positive.
    have h_singleton_pos : 0 < mu {a} := by
      simp +decide [ mu ];
    exact h_singleton_pos;
    aesop;
  -- To prove that two functions are equal, we can use the ext tactic, which allows us to show that they are equal at every point.
  ext a; exact h_eq a

/-- (Σ f)² ≤ n · Σ f² via Cauchy-Schwarz -/
lemma sum_sq_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
      exact?

lemma potentialNeighbors_finite (u : ℂ) : (potentialNeighbors u).Finite :=
  Set.Finite.union (Set.finite_range _) (Set.finite_range _)

/-- lintegral under counting measure = tsum -/
lemma lintegral_count_eq_tsum (f : Vertices → ENNReal) :
    lintegral mu f = ∑' x, f x := by
      -- Apply the theorem that states the integral of a function with respect to the counting measure is the sum of the function over the set. This is a standard result in measure theory, and in Lean, it's probably something like `MeasureTheory.lintegral_count`.
      apply MeasureTheory.lintegral_count

/-- Every vertex has finitely many neighbors -/
instance (v : Vertices) : Finite (PenroseGraph.neighborSet v) := by
  apply Set.Finite.of_finite_image _ (fun x _ y _ h => Subtype.eq h)
  exact Set.Finite.subset (potentialNeighbors_finite v.1)
    (by rintro _ ⟨w, hw, rfl⟩; exact neighbor_subset v hw)

#check PenroseGraph.LocallyFinite

variable (u : Vertices)
#check Fintype.ofFinite (PenroseGraph.neighborSet u)

noncomputable instance (u : Vertices) : Fintype (PenroseGraph.neighborSet u) :=
  Fintype.ofFinite (PenroseGraph.neighborSet u)

/-- **DEGREE BOUND**: deg(u) ≤ 10 -/
theorem degree_bound (u : Vertices) : PenroseGraph.degree u ≤ 10 := by
  -- The potential neighbors set is the union of two ranges, each with 5 elements, so its cardinality is 10.
  have h_potential_neighbors_card : (potentialNeighbors u.1).ncard ≤ 10 := by
    have h_card : (potentialNeighbors u.1).ncard ≤ Finset.card (Finset.image (fun k : Fin 5 => u.1 + pentagonVertex k) Finset.univ ∪ Finset.image (fun k : Fin 5 => u.1 - pentagonVertex k) Finset.univ) := by
      rw [ ← Set.ncard_coe_finset ] ; aesop;
    exact h_card.trans ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( Finset.card_image_le ) ( Finset.card_image_le ) ) );
  have h_degree_le_potential_neighbors_card : (PenroseGraph.neighborSet u).ncard ≤ (potentialNeighbors u.1).ncard := by
    apply Set.ncard_le_ncard_of_injOn;
    case f => exact fun x => x.1;
    · -- By definition of PenroseGraph, if a is adjacent to u, then there exists some k such that a = u + pentagonVertex k or a = u - pentagonVertex k.
      intro a ha
      obtain ⟨k, hk⟩ := ha;
      exact hk.elim ( fun hk => Or.inl ⟨ k, by aesop ⟩ ) fun hk => Or.inr ⟨ k, by aesop ⟩;
    · exact fun x hx y hy hxy => Subtype.ext hxy;
    · exact potentialNeighbors_finite u.1;
  have key : (PenroseGraph.neighborSet u).ncard ≤ 10 :=
    h_degree_le_potential_neighbors_card.trans h_potential_neighbors_card
  show (PenroseGraph.neighborFinset u).card ≤ 10
  rw [SimpleGraph.neighborFinset_def, ← Set.ncard_eq_toFinset_card']
  exact key

variable (u : Vertices)
#synth Fintype (PenroseGraph.neighborSet u)

/-! ### Adjacency operator A -/

/-- Raw adjacency: (A f)(u) = Σ_{v ~ u} f(v) -/
def A_raw (f : Vertices → ℂ) (u : Vertices) : ℂ :=
  ∑ v ∈ PenroseGraph.neighborFinset u, f v

/-- Pointwise bound: ‖A f u‖² ≤ 10 · Σ_{v~u} ‖f v‖² -/
lemma A_raw_ptwise_bound (f : Vertices → ℂ) (u : Vertices) :
    ‖A_raw f u‖ ^ 2 ≤ 10 * ∑ v ∈ PenroseGraph.neighborFinset u, ‖f v‖ ^ 2 := by
      -- By the properties of the adjacency matrix and the degree bound, we can show that the energy of A is controlled by the energy of f. Specifically, we have:
      have h_energy : ‖A_raw f u‖ ^ 2 ≤ (Finset.card (PenroseGraph.neighborFinset u)) * ∑ v ∈ PenroseGraph.neighborFinset u, ‖f v‖ ^ 2 := by
        have h_triangle : ‖A_raw f u‖ ^ 2 ≤ (Finset.sum (PenroseGraph.neighborFinset u) (fun v => ‖f v‖)) ^ 2 := by
          gcongr;
          exact norm_sum_le _ _;
        refine le_trans h_triangle ?_;
        exact?;
      exact h_energy.trans ( mul_le_mul_of_nonneg_right ( mod_cast degree_bound u ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) )

#check A_raw

/-- Adjacency operator is bounded: ‖A f‖_{ℓ²} ≤ 10 · ‖f‖_{ℓ²} -/
lemma A_raw_bound (f : Vertices → ℂ) :
    eLpNorm (A_raw f) 2 mu ≤ 10 * eLpNorm f 2 mu := by
      rw [ MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm, MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm ] <;> norm_num +zetaDelta at *;
      -- Apply the pointwise bound to each term in the sum.
      have h_sum_bound : ∀ u : Vertices, ‖A_raw f u‖ₑ ^ 2 ≤ 10 * ∑ v ∈ PenroseGraph.neighborFinset u, ‖f v‖ₑ ^ 2 := by
        intro u
        have h_sum_bound : ‖A_raw f u‖^2 ≤ 10 * ∑ v ∈ PenroseGraph.neighborFinset u, ‖f v‖^2 := by
          exact?;
        convert ENNReal.ofReal_le_ofReal h_sum_bound using 1;
        · norm_num [ ← ENNReal.ofReal_coe_nnreal ];
        · norm_num [ ENNReal.ofReal_mul, ENNReal.ofReal_sum_of_nonneg, sq_nonneg ];
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∫⁻ (x : Vertices), ∑ v ∈ PenroseGraph.neighborFinset x, ‖f v‖ₑ ^ 2 ∂mu = ∫⁻ (v : Vertices), ‖f v‖ₑ ^ 2 * (PenroseGraph.degree v) ∂mu := by
        have h_fubini : ∫⁻ (x : Vertices), ∑ v ∈ PenroseGraph.neighborFinset x, ‖f v‖ₑ ^ 2 ∂mu = ∑' (v : Vertices), ‖f v‖ₑ ^ 2 * (PenroseGraph.degree v) := by
          have h_fubini : ∫⁻ (x : Vertices), ∑ v ∈ PenroseGraph.neighborFinset x, ‖f v‖ₑ ^ 2 ∂mu = ∑' (v : Vertices), ∑' (x : Vertices), ‖f v‖ₑ ^ 2 * (if x ∈ PenroseGraph.neighborFinset v then 1 else 0) := by
            have h_fubini : ∫⁻ (x : Vertices), ∑ v ∈ PenroseGraph.neighborFinset x, ‖f v‖ₑ ^ 2 ∂mu = ∑' (x : Vertices), ∑' (v : Vertices), ‖f v‖ₑ ^ 2 * (if x ∈ PenroseGraph.neighborFinset v then 1 else 0) := by
              have h_fubini : ∀ x : Vertices, ∑ v ∈ PenroseGraph.neighborFinset x, ‖f v‖ₑ ^ 2 = ∑' (v : Vertices), ‖f v‖ₑ ^ 2 * (if x ∈ PenroseGraph.neighborFinset v then 1 else 0) := by
                intro x; rw [ tsum_eq_sum ];
                congr! 1;
                · simp +zetaDelta at *;
                  exact fun h => False.elim <| h <| by tauto;
                · simp +contextual [ SimpleGraph.adj_comm ]
              simp +decide only [h_fubini, lintegral_count_eq_tsum];
            rw [ h_fubini, ← ENNReal.tsum_comm ];
          simp_all +decide [ Finset.sum_ite ];
          refine' tsum_congr fun v => _;
          rw [ tsum_eq_sum ];
          any_goals exact PenroseGraph.neighborFinset v;
          · rw [ Finset.sum_congr rfl fun x hx => if_pos <| by simpa using hx ] ; norm_num [ mul_comm ];
          · simp +contextual [ SimpleGraph.neighborFinset ];
        convert h_fubini using 1;
        erw [ MeasureTheory.lintegral_count ];
      -- Apply the bound on the degree to the integral.
      have h_degree_bound : ∫⁻ (v : Vertices), ‖f v‖ₑ ^ 2 * (PenroseGraph.degree v) ∂mu ≤ 10 * ∫⁻ (v : Vertices), ‖f v‖ₑ ^ 2 ∂mu := by
        rw [ ← MeasureTheory.lintegral_const_mul ];
        · refine' MeasureTheory.lintegral_mono fun v => _;
          rw [ mul_comm ] ; gcongr ; norm_cast ; exact degree_bound v |> le_trans <| by norm_num;
        · fun_prop (disch := solve_by_elim);
      refine' le_trans ( ENNReal.rpow_le_rpow ( MeasureTheory.lintegral_mono h_sum_bound ) ( by norm_num ) ) _;
      rw [ MeasureTheory.lintegral_const_mul' ] <;> norm_num [ h_fubini, h_degree_bound ];
      rw [ ENNReal.mul_rpow_of_nonneg ] <;> norm_num;
      refine' le_trans ( mul_le_mul_left' ( ENNReal.rpow_le_rpow h_degree_bound ( by norm_num ) ) _ ) _;
      rw [ ENNReal.mul_rpow_of_nonneg ] <;> norm_num;
      rw [ ← mul_assoc, ← ENNReal.rpow_add ] <;> norm_num

/-- Adjacency preserves ℓ² membership -/
lemma memLp_A_raw {f : Vertices → ℂ} (hf : MemLp f 2 mu) :
    MemLp (A_raw f) 2 mu := by
      -- Since the adjacency operator is linear and bounded, it maps L² functions to L² functions. Therefore, A_raw f is in L² if f is in L².
      have h_bounded : ∀ f : Vertices → ℂ, MeasureTheory.MemLp f 2 mu → MeasureTheory.MemLp (A_raw f) 2 mu := by
        intro f hf
        have h_A_raw_f_L2 : eLpNorm (A_raw f) 2 mu ≤ 10 * eLpNorm f 2 mu := by
          exact?;
        constructor;
        · exact?;
        · exact lt_of_le_of_lt h_A_raw_f_L2 ( ENNReal.mul_lt_top ( by norm_num ) ( hf.eLpNorm_lt_top ) );
      exact h_bounded f hf

#check A_raw_ptwise_bound

#check memLp_A_raw

/-- Adjacency on AEEqFun quotient -/
def A_ae : (Vertices →ₘ[mu] ℂ) → (Vertices →ₘ[mu] ℂ) :=
  Quotient.lift
    (fun f : { f : Vertices → ℂ // AEStronglyMeasurable f mu } =>
      AEEqFun.mk (A_raw f.1)
        (Measurable.aestronglyMeasurable (measurable_of_countable _)))
    (fun f g h => AEEqFun.mk_eq_mk.mpr (by rw [ae_eq_of_count h]))

/-- coeFn of `A_ae` is the raw operator (strict eq under counting measure) -/
lemma A_ae_coeFn (x : Vertices →ₘ[mu] ℂ) : (⇑(A_ae x) : Vertices → ℂ) = A_raw ⇑x := by
  induction x using MeasureTheory.AEEqFun.induction_on with
  | _ g hg =>
    apply ae_eq_of_count
    have h1 : (⇑(A_ae (AEEqFun.mk g hg)) : Vertices → ℂ) =ᵐ[mu] A_raw g := AEEqFun.coeFn_mk _ _
    have h2 : (⇑(AEEqFun.mk g hg) : Vertices → ℂ) = g := ae_eq_of_count (AEEqFun.coeFn_mk g hg)
    rw [h2]; exact h1

lemma A_ae_add (f g : Vertices →ₘ[mu] ℂ) : A_ae (f + g) = A_ae f + A_ae g := by
  apply MeasureTheory.AEEqFun.ext
  have e2 : (⇑(A_ae f + A_ae g) : Vertices → ℂ) = A_raw ⇑f + A_raw ⇑g := by
    rw [ae_eq_of_count (AEEqFun.coeFn_add (A_ae f) (A_ae g)), A_ae_coeFn, A_ae_coeFn]
  have e3 : (⇑(f + g) : Vertices → ℂ) = ⇑f + ⇑g := ae_eq_of_count (AEEqFun.coeFn_add f g)
  have e4 : A_raw (⇑f + ⇑g) = A_raw ⇑f + A_raw ⇑g := by
    funext u; simp only [A_raw, Pi.add_apply]; rw [Finset.sum_add_distrib]
  rw [A_ae_coeFn, e3, e4, ← e2]

lemma A_ae_smul (c : ℂ) (f : Vertices →ₘ[mu] ℂ) : A_ae (c • f) = c • A_ae f := by
  apply MeasureTheory.AEEqFun.ext
  have e2 : (⇑(c • A_ae f) : Vertices → ℂ) = c • A_raw ⇑f := by
    rw [ae_eq_of_count (AEEqFun.coeFn_smul c (A_ae f)), A_ae_coeFn]
  have e3 : (⇑(c • f) : Vertices → ℂ) = c • ⇑f := ae_eq_of_count (AEEqFun.coeFn_smul c f)
  have e4 : A_raw (c • ⇑f) = c • A_raw ⇑f := by
    funext u; simp only [A_raw, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [A_ae_coeFn, e3, e4, ← e2]

lemma A_ae_memLp (f : Vertices →ₘ[mu] ℂ) (hf : f ∈ Lp ℂ 2 mu) :
    A_ae f ∈ Lp ℂ 2 mu := by
      have h_Aaef_L2 : ∀ f : Vertices → ℂ, MemLp f 2 mu → MemLp (A_raw f) 2 mu := by
        exact?;
      obtain ⟨ g, hg ⟩ := f;
      rw [ MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top ] at *;
      convert h_Aaef_L2 g _ |> fun h => h.2 using 1;
      · erw [ MeasureTheory.eLpNorm_congr_ae ( MeasureTheory.AEEqFun.coeFn_mk _ _ ) ];
      · constructor <;> aesop

/-- **ADJACENCY OPERATOR**: A : ℓ² → ℓ² -/
def A : L2 →ₗ[ℂ] L2 where
  toFun f := ⟨A_ae f.1, A_ae_memLp f.1 f.2⟩
  map_add' f g := Subtype.eq (A_ae_add f.1 g.1)
  map_smul' c f := Subtype.eq (A_ae_smul c f.1)

/-! ### Degree operator D -/

/-- Degree as ℂ -/
def deg_fn (u : Vertices) : ℂ := (PenroseGraph.degree u : ℂ)

lemma deg_fn_bound (u : Vertices) : ‖deg_fn u‖ ≤ 10 := by
  simp [deg_fn]; exact_mod_cast degree_bound u

/-- Raw degree operator: (D f)(u) = deg(u) · f(u) -/
def D_raw (f : Vertices → ℂ) (u : Vertices) : ℂ := deg_fn u * f u

lemma D_raw_bound_ptwise (f : Vertices → ℂ) (u : Vertices) :
    ‖D_raw f u‖ ≤ 10 * ‖f u‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (deg_fn_bound u) (norm_nonneg _))

lemma D_raw_norm_bound (f : Vertices → ℂ) :
    eLpNorm (D_raw f) 2 mu ≤ 10 * eLpNorm f 2 mu := by
      -- Apply the pointwise bound to each term in the sum.
      have h_sum_bound : ∀ u : Vertices, ‖D_raw f u‖ ^ 2 ≤ 10 ^ 2 * ‖f u‖ ^ 2 := by
        exact fun u => by rw [ D_raw ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( D_raw_bound_ptwise f u ) 2 ) ( by ring_nf; norm_num ) ;
      have h_sum_bound : ∫⁻ u, ENNReal.ofReal (‖D_raw f u‖ ^ 2) ∂mu ≤ 10 ^ 2 * ∫⁻ u, ENNReal.ofReal (‖f u‖ ^ 2) ∂mu := by
        rw [ ← MeasureTheory.lintegral_const_mul' ];
        · refine' MeasureTheory.lintegral_mono fun u => _;
          convert ENNReal.ofReal_le_ofReal ( h_sum_bound u ) using 1 ; norm_num [ ENNReal.ofReal_mul ];
        · norm_num;
      simp_all +decide [ MeasureTheory.eLpNorm, MeasureTheory.eLpNorm' ];
      convert ENNReal.rpow_le_rpow h_sum_bound _ using 1 ; norm_num [ ← ENNReal.mul_rpow_of_nonneg ];
      · rw [ ENNReal.mul_rpow_of_nonneg ] <;> norm_num;
        rw [ show ( 100 : ENNReal ) = 10 ^ 2 by norm_num, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul ] ; norm_num;
      · norm_num

lemma memLp_D_raw {f : Vertices → ℂ} (hf : MemLp f 2 mu) : MemLp (D_raw f) 2 mu := by
  refine' ⟨ _, _ ⟩;
  · exact?;
  · refine' lt_of_le_of_lt ( D_raw_norm_bound f ) _;
    exact ENNReal.mul_lt_top ( by norm_num ) ( hf.eLpNorm_lt_top )

/-- Degree on AEEqFun quotient -/
def D_ae : (Vertices →ₘ[mu] ℂ) → (Vertices →ₘ[mu] ℂ) :=
  Quotient.lift
    (fun f : { f : Vertices → ℂ // AEStronglyMeasurable f mu } =>
      AEEqFun.mk (D_raw f.1)
        (Measurable.aestronglyMeasurable (measurable_of_countable _)))
    (fun f g h => AEEqFun.mk_eq_mk.mpr (by rw [ae_eq_of_count h]))

/-- coeFn of `D_ae` is the raw operator (strict eq under counting measure) -/
lemma D_ae_coeFn (x : Vertices →ₘ[mu] ℂ) : (⇑(D_ae x) : Vertices → ℂ) = D_raw ⇑x := by
  induction x using MeasureTheory.AEEqFun.induction_on with
  | _ g hg =>
    apply ae_eq_of_count
    have h1 : (⇑(D_ae (AEEqFun.mk g hg)) : Vertices → ℂ) =ᵐ[mu] D_raw g := AEEqFun.coeFn_mk _ _
    have h2 : (⇑(AEEqFun.mk g hg) : Vertices → ℂ) = g := ae_eq_of_count (AEEqFun.coeFn_mk g hg)
    rw [h2]; exact h1

lemma D_ae_add (f g : Vertices →ₘ[mu] ℂ) : D_ae (f + g) = D_ae f + D_ae g := by
  apply MeasureTheory.AEEqFun.ext
  have e2 : (⇑(D_ae f + D_ae g) : Vertices → ℂ) = D_raw ⇑f + D_raw ⇑g := by
    rw [ae_eq_of_count (AEEqFun.coeFn_add (D_ae f) (D_ae g)), D_ae_coeFn, D_ae_coeFn]
  have e3 : (⇑(f + g) : Vertices → ℂ) = ⇑f + ⇑g := ae_eq_of_count (AEEqFun.coeFn_add f g)
  have e4 : D_raw (⇑f + ⇑g) = D_raw ⇑f + D_raw ⇑g := by
    funext u; simp only [D_raw, Pi.add_apply, mul_add]
  rw [D_ae_coeFn, e3, e4, ← e2]

lemma D_ae_smul (c : ℂ) (f : Vertices →ₘ[mu] ℂ) : D_ae (c • f) = c • D_ae f := by
  apply MeasureTheory.AEEqFun.ext
  have e2 : (⇑(c • D_ae f) : Vertices → ℂ) = c • D_raw ⇑f := by
    rw [ae_eq_of_count (AEEqFun.coeFn_smul c (D_ae f)), D_ae_coeFn]
  have e3 : (⇑(c • f) : Vertices → ℂ) = c • ⇑f := ae_eq_of_count (AEEqFun.coeFn_smul c f)
  have e4 : D_raw (c • ⇑f) = c • D_raw ⇑f := by
    funext u; simp only [D_raw, Pi.smul_apply, smul_eq_mul]; ring
  rw [D_ae_coeFn, e3, e4, ← e2]

lemma D_ae_memLp (f : Vertices →ₘ[mu] ℂ) (hf : f ∈ Lp ℂ 2 mu) :
    D_ae f ∈ Lp ℂ 2 mu := by
      -- Since $D_ae$ is a linear operator and $f$ is in $Lp$, it follows that $D_ae f$ is also in $Lp$.
      have hD_ae_Lp : ∀ f : Vertices →ₘ[mu] ℂ, f ∈ MeasureTheory.Lp ℂ 2 mu → D_ae f ∈ MeasureTheory.Lp ℂ 2 mu := by
        intro f hf;
        obtain ⟨ g, hg ⟩ := f;
        convert memLp_D_raw _;
        rw [ MeasureTheory.Lp.mem_Lp_iff_memLp ];
        rotate_left;
        exact g;
        · rw [ MeasureTheory.MemLp ];
          rw [ MeasureTheory.Lp.mem_Lp_iff_eLpNorm_lt_top ] at hf ; aesop;
        · erw [ MeasureTheory.memLp_congr_ae ];
          exact MeasureTheory.AEEqFun.coeFn_mk _ _;
      exact hD_ae_Lp f hf

/-- **DEGREE OPERATOR**: D : ℓ² → ℓ² -/
def D : L2 →ₗ[ℂ] L2 where
  toFun f := ⟨D_ae f.1, D_ae_memLp f.1 f.2⟩
  map_add' f g := Subtype.eq (D_ae_add f.1 g.1)
  map_smul' c f := Subtype.eq (D_ae_smul c f.1)

lemma norm_D_le (f : L2) : ‖D f‖ ≤ 10 * ‖f‖ := by
  -- By definition of $D$, we know that $\|D f\| \leq 10 \|f\|$.
  have hD : ∀ f : Vertices → ℂ, MemLp f 2 mu → eLpNorm (D_raw f) 2 mu ≤ 10 * eLpNorm f 2 mu := by
    exact?;
  convert hD _ _ using 1;
  rotate_left;
  exact fun x => f.1 x;
  · exact?;
  · simp +decide [ Norm.norm, MeasureTheory.Lp ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · congr! 2;
      -- Since $D_ae$ is defined as the lift of $D_raw$, and the lift preserves the eLpNorm, this should hold.
      have h_lift : ∀ f : Vertices → ℂ, MemLp f 2 mu → eLpNorm (D_ae (AEEqFun.mk f (Measurable.aestronglyMeasurable (measurable_of_countable _)))) 2 mu = eLpNorm (D_raw f) 2 mu := by
        intro f hf; exact (by
        rw [ MeasureTheory.eLpNorm_congr_ae ];
        exact AEEqFun.coeFn_mk _ _);
      convert h_lift _ _;
      · -- By definition of $D$, we know that $D f$ is the lift of $D_ae$ applied to the AEEqFun.mk of $f$'s underlying function.
        simp [D];
      · exact?;
    · refine' ne_of_lt ( lt_of_le_of_lt ( hD _ _ ) _ );
      · exact?;
      · exact ENNReal.mul_lt_top ENNReal.coe_lt_top ( MeasureTheory.Lp.eLpNorm_lt_top _ );
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( MeasureTheory.Lp.memLp _ |> fun h => h.eLpNorm_ne_top )

lemma norm_A_le (f : L2) : ‖A f‖ ≤ 10 * ‖f‖ := by
  -- Apply the lemma A_raw_bound to conclude the proof.
  have h_norm_A : ‖A f‖ ≤ 10 * ‖f‖ := by
    have := A_raw_bound f.1
    convert this using 1;
    norm_num [ Norm.norm ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · congr! 2;
      -- Since A_ae is the lift of A_raw, their eLpNorms are equal.
      have h_eq : ∀ f : Vertices → ℂ, eLpNorm (A_ae (AEEqFun.mk f (by
      exact?))) 2 mu = eLpNorm (A_raw f) 2 mu := by
        intro f; exact (by
        rw [ MeasureTheory.eLpNorm_congr_ae ];
        exact AEEqFun.coeFn_mk _ _ |> fun h => h.mono fun x hx => by aesop;)
      generalize_proofs at *;
      convert h_eq f.1 using 1;
      -- Since A is defined as the lift of A_ae, their actions on the functions should be the same. Therefore, the equality holds by definition.
      simp [A];
    · refine' ne_of_lt ( lt_of_le_of_lt this _ );
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top ( MeasureTheory.Lp.memLp _ |> fun h => h.eLpNorm_lt_top );
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( by exact? );
  exact h_norm_A

/-- **THE GRAPH LAPLACIAN**: Δ = D − A -/
def Delta : L2 →ₗ[ℂ] L2 := D - A

/-- **BOUNDEDNESS**: ‖Δ f‖ ≤ 20 · ‖f‖ -/
theorem Delta_bounded : ∃ C : ℝ, 0 < C ∧ ∀ f : L2, ‖Delta f‖ ≤ C * ‖f‖ :=
  ⟨20, by norm_num, fun f =>
    calc ‖Delta f‖ = ‖D f - A f‖        := rfl
      _ ≤ ‖D f‖ + ‖A f‖             := norm_sub_le _ _
      _ ≤ 10 * ‖f‖ + 10 * ‖f‖       := add_le_add (norm_D_le f) (norm_A_le f)
      _ = 20 * ‖f‖                   := by ring⟩

lemma lintegral_sum_neighbors_le (f : Vertices → ENNReal) :
    MeasureTheory.lintegral mu (fun u => Finset.sum (PenroseGraph.neighborFinset u) (fun v => f v)) ≤
    10 * MeasureTheory.lintegral mu f := by
      by_contra h_contra;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∫⁻ (u : Vertices), ∑ v ∈ PenroseGraph.neighborFinset u, f v ∂mu = ∑' v, ∑' u, f v * (if v ∈ PenroseGraph.neighborFinset u then 1 else 0) := by
        have h_fubini : ∫⁻ (u : Vertices), ∑ v ∈ PenroseGraph.neighborFinset u, f v ∂mu = ∑' v, ∫⁻ (u : Vertices), f v * (if v ∈ PenroseGraph.neighborFinset u then 1 else 0) ∂mu := by
          rw [ ← MeasureTheory.lintegral_tsum ];
          · congr with u ; rw [ tsum_eq_sum ];
            exacts [ Finset.sum_congr rfl fun v hv => by rw [ if_pos hv, mul_one ], fun v hv => by rw [ if_neg hv, MulZeroClass.mul_zero ] ];
          · exact?;
        convert h_fubini using 3;
        erw [ MeasureTheory.lintegral_count ];
      -- Since each vertex has at most 10 neighbors, the inner sum $\sum' u, f v * (if v ∈ PenroseGraph.neighborFinset u then 1 else 0)$ is at most $10 * f v$.
      have h_bound : ∀ v : Vertices, ∑' u : Vertices, f v * (if v ∈ PenroseGraph.neighborFinset u then 1 else 0) ≤ 10 * f v := by
        intro v;
        rw [ ENNReal.tsum_eq_iSup_sum ];
        refine' iSup_le fun s => _;
        simp +decide [ mul_comm, Finset.sum_ite ];
        gcongr;
        refine' mod_cast le_trans ( Finset.card_le_card _ ) _;
        exact PenroseGraph.neighborFinset v;
        · simp +decide [ Finset.subset_iff, SimpleGraph.adj_comm ];
        · exact degree_bound v;
      refine' h_contra _;
      convert ENNReal.tsum_le_tsum h_bound using 1;
      rw [ ENNReal.tsum_mul_left ];
      erw [ MeasureTheory.lintegral_count ]

-- Final sanity checks
#check @Delta_bounded
#check @degree_bound
#check @rotation_is_multiplication
#check @zeta5_pow_five
#check @adjacent_symm

end Brockian.Penrose
