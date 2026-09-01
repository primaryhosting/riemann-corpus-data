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
# Symmetric operators, deficiency spaces and the basic criterion of essential self-adjointness

This file develops the small amount of unbounded-operator theory that is needed to state and
prove that a Schrödinger operator is essentially self-adjoint.

An *operator with domain `D`* on a complex Hilbert space `H` is encoded here as a pair of
linear maps `ι T : D →ₗ[ℂ] H`, where `ι` describes how the (abstract) domain `D` sits inside
`H` and `T` is the action of the operator.  (Taking `D` to be a submodule of `H` and `ι` its
inclusion recovers the usual picture; the extra generality is convenient because the natural
domain of a Schrödinger operator is a space of Schwartz functions.)

The main definition is `Brockian.Weyl.IsEssentiallySelfAdjoint`, which is the classical *basic
criterion* of von Neumann (see e.g. Reed–Simon, *Methods of Modern Mathematical Physics I*,
Theorem VIII.3): a densely defined symmetric operator is essentially self-adjoint if and only
if the ranges of `T + i` and `T - i` are dense.  The theorem
`Brockian.Weyl.dense_range_smul_sub_iff_deficiency` records the equivalent formulation in terms
of the *deficiency spaces*: no nonzero `v ∈ H` solves the weak (adjoint) equation `T* v = ∓ i v`.

The remaining results are the analytic tools used later:

* `Brockian.Weyl.norm_add_I_smul_lower_bound`: the basic lower bound `‖T x + i b ι x‖ ≥ |b| ‖ι x‖`
  for a symmetric operator;
* `Brockian.Weyl.dense_range_add_of_relatively_bounded`: a small perturbation lemma, which is the
  engine both of the Kato–Rellich argument and of the transfer of density in the spectral
  parameter;
* `Brockian.Weyl.dense_range_shift_of_dense_range_shift`: density of the range of `T + i b'`
  follows from density of the range of `T + i b` whenever `|b' - b| < b`.
-/

noncomputable section

open scoped ComplexInnerProductSpace

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- An operator `T` with domain described by `ι` is *symmetric* if `⟪T x, ι y⟫ = ⟪ι x, T y⟫`. -/
def IsSymmetricOn (ι T : D →ₗ[ℂ] H) : Prop :=
  ∀ x y : D, ⟪T x, ι y⟫ = ⟪ι x, T y⟫

/-- The operator `T + i b` (with domain described by `ι`), for a real parameter `b`. -/
def shift (ι T : D →ₗ[ℂ] H) (b : ℝ) : D →ₗ[ℂ] H := T + ((b : ℂ) * Complex.I) • ι

@[simp] lemma shift_apply (ι T : D →ₗ[ℂ] H) (b : ℝ) (x : D) :
    shift ι T b x = T x + ((b : ℂ) * Complex.I) • ι x := rfl

/-- **Essential self-adjointness**, in the form of von Neumann's basic criterion: the operator
`T` with (dense) domain described by `ι` is symmetric and the ranges of `T + i` and of `T - i`
are dense.  For a densely defined symmetric operator this is equivalent to the closure of `T`
being self-adjoint. -/
structure IsEssentiallySelfAdjoint (ι T : D →ₗ[ℂ] H) : Prop where
  /-- The domain is dense in `H`. -/
  dense_domain : Dense (Set.range ι)
  /-- The operator is symmetric. -/
  symmetric : IsSymmetricOn ι T
  /-- The range of `T + i` is dense. -/
  dense_range_add_I : Dense (Set.range fun x => T x + Complex.I • ι x)
  /-- The range of `T - i` is dense. -/
  dense_range_sub_I : Dense (Set.range fun x => T x - Complex.I • ι x)

section Complete

variable [CompleteSpace H]

/-- A linear map into a Hilbert space has dense range iff no nonzero vector is orthogonal to
its range. -/
theorem dense_range_iff_forall_inner_eq_zero (f : D →ₗ[ℂ] H) :
    Dense (Set.range f) ↔ ∀ v : H, (∀ x, ⟪f x, v⟫ = 0) → v = 0 := by
  have hset : ((LinearMap.range f : Submodule ℂ H) : Set H) = Set.range f := by
    ext v; simp [LinearMap.mem_range]
  constructor
  · intro hdense v hv
    have h0 : ⟪v, v⟫ = (0 : ℂ) := by
      have hc : Continuous fun w : H => ⟪w, v⟫ :=
        continuous_inner.comp (Continuous.prodMk continuous_id continuous_const)
      have : ∀ w ∈ closure (Set.range f), ⟪w, v⟫ = (0 : ℂ) := by
        intro w hw
        refine (isClosed_eq hc continuous_const).closure_subset_iff.2 ?_ hw
        rintro _ ⟨x, rfl⟩; exact hv x
      exact this v (by rw [hdense.closure_eq]; trivial)
    simpa using inner_self_eq_zero.1 h0
  · intro h
    have hbot : (LinearMap.range f : Submodule ℂ H)ᗮ = ⊥ := by
      refine Submodule.eq_bot_iff _ |>.2 fun v hv => ?_
      exact h v fun x => hv (f x) ⟨x, rfl⟩
    have := (Submodule.topologicalClosure_eq_top_iff (K := (LinearMap.range f : Submodule ℂ H))).2
      hbot
    have hcl : closure (Set.range f) = Set.univ := by
      have : ((LinearMap.range f : Submodule ℂ H).topologicalClosure : Set H) = Set.univ := by
        rw [this]; rfl
      rwa [Submodule.topologicalClosure_coe, hset] at this
    exact dense_iff_closure_eq.2 hcl

/-- The deficiency-space formulation of density of the range of `T - z`: the range of `T - z`
is dense if and only if the *deficiency equation* `T* v = conj z • v`, read weakly, has no
nonzero solution. -/
theorem dense_range_smul_sub_iff_deficiency (ι T : D →ₗ[ℂ] H) (z : ℂ) :
    Dense (Set.range fun x => T x - z • ι x) ↔
      ∀ v : H, (∀ x, ⟪T x, v⟫ = (starRingEnd ℂ) z * ⟪ι x, v⟫) → v = 0 := by
  have key := dense_range_iff_forall_inner_eq_zero (T - z • ι)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply] at key
  rw [show (fun x => T x - z • ι x) = ⇑(T - z • ι) from rfl, key]
  constructor
  · intro h v hv
    refine h v fun x => ?_
    rw [inner_sub_left, inner_smul_left, hv x]
    ring
  · intro h v hv
    refine h v fun x => ?_
    have := hv x
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at this
    simpa using this

end Complete

section Symmetric

variable {ι T : D →ₗ[ℂ] H}

/-- For a symmetric operator, `⟪T x, ι x⟫` is real. -/
lemma inner_apply_isReal (hsym : IsSymmetricOn ι T) (x : D) :
    (starRingEnd ℂ) ⟪T x, ι x⟫ = ⟪T x, ι x⟫ := by
  rw [← inner_conj_symm (𝕜 := ℂ) (T x) (ι x)]
  simp [hsym x x]

/-- The Pythagoras identity `‖T x + i b ι x‖² = ‖T x‖² + b² ‖ι x‖²` for a symmetric operator. -/
lemma norm_add_I_smul_sq (hsym : IsSymmetricOn ι T) (b : ℝ) (x : D) :
    ‖T x + ((b : ℂ) * Complex.I) • ι x‖ ^ 2 = ‖T x‖ ^ 2 + b ^ 2 * ‖ι x‖ ^ 2 := by
  have hre : (⟪T x, ι x⟫ : ℂ).im = 0 := by
    have h := congrArg Complex.im (inner_apply_isReal hsym x)
    simp only [Complex.conj_im] at h
    linarith
  have hcross : (2 : ℝ) * (inner ℂ (T x) (((b : ℂ) * Complex.I) • ι x)).re = 0 := by
    rw [inner_smul_right, Complex.mul_re]
    simp [Complex.mul_re, Complex.mul_im, hre]
  have hnorm : ‖T x + ((b : ℂ) * Complex.I) • ι x‖ ^ 2
      = ‖T x‖ ^ 2 + 2 * (inner ℂ (T x) (((b : ℂ) * Complex.I) • ι x)).re
        + ‖((b : ℂ) * Complex.I) • ι x‖ ^ 2 := by
    rw [@norm_add_sq ℂ]
    simp [RCLike.re_to_complex, inner_smul_right, Complex.mul_re, Complex.mul_im, hre]
  rw [hnorm, hcross]
  have hns : ‖((b : ℂ) * Complex.I) • ι x‖ = |b| * ‖ι x‖ := by
    rw [norm_smul]
    simp
  rw [hns]
  rw [mul_pow, sq_abs]
  ring

/-- The basic lower bound for a symmetric operator: `‖T x + i b ι x‖ ≥ |b| ‖ι x‖`. -/
theorem norm_add_I_smul_lower_bound (hsym : IsSymmetricOn ι T) (b : ℝ) (x : D) :
    |b| * ‖ι x‖ ≤ ‖T x + ((b : ℂ) * Complex.I) • ι x‖ := by
  have h := norm_add_I_smul_sq hsym b x
  have h1 : (|b| * ‖ι x‖) ^ 2 ≤ ‖T x + ((b : ℂ) * Complex.I) • ι x‖ ^ 2 := by
    rw [h, mul_pow, sq_abs]
    nlinarith [sq_nonneg ‖T x‖]
  have h2 : (0 : ℝ) ≤ ‖T x + ((b : ℂ) * Complex.I) • ι x‖ := norm_nonneg _
  nlinarith [abs_nonneg b, norm_nonneg (ι x), mul_nonneg (abs_nonneg b) (norm_nonneg (ι x))]

end Symmetric

section Perturbation

variable [CompleteSpace H]

/-- **Perturbation lemma.** If `A` has dense range and `B` is `A`-bounded with relative bound
`c < 1`, then `A + B` has dense range. -/
theorem dense_range_add_of_relatively_bounded (A B : D →ₗ[ℂ] H) {c : ℝ} (hc : c < 1)
    (hB : ∀ x, ‖B x‖ ≤ c * ‖A x‖) (hA : Dense (Set.range A)) :
    Dense (Set.range fun x => A x + B x) := by
  -- we may assume `0 ≤ c`
  set c' : ℝ := max c 0 with hc'
  have hc'1 : c' < 1 := max_lt hc one_pos
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hB' : ∀ x, ‖B x‖ ≤ c' * ‖A x‖ := fun x =>
    (hB x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have key := dense_range_iff_forall_inner_eq_zero (A + B)
  simp only [LinearMap.add_apply] at key
  rw [show (fun x => A x + B x) = ⇑(A + B) from rfl, key]
  intro v hv
  by_contra hv0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have main : ∀ ε > (0 : ℝ), (1 - c') * ‖v‖ ≤ ε * (1 + c') := by
    intro ε hε
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (hA.closure_eq ▸ Set.mem_univ v) ε hε
    have hdist : ‖A x - v‖ < ε := by
      rw [← dist_eq_norm]; simpa [dist_comm] using hx
    have hAx : ‖A x‖ ≤ ‖v‖ + ε := by
      have := norm_sub_norm_le (A x) v
      linarith
    have h0 : ⟪A x, v⟫ + ⟪B x, v⟫ = 0 := by
      have := hv x
      rwa [inner_add_left] at this
    have e1 : ⟪A x, v⟫ = ⟪A x - v, v⟫ + ⟪v, v⟫ := by
      rw [inner_sub_left]; ring
    have hb1 : ‖⟪A x - v, v⟫‖ ≤ ε * ‖v‖ := by
      refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
      exact mul_le_mul_of_nonneg_right hdist.le (norm_nonneg _)
    have hb2 : ‖⟪B x, v⟫‖ ≤ c' * (‖v‖ + ε) * ‖v‖ := by
      refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
      have hbx : ‖B x‖ ≤ c' * (‖v‖ + ε) :=
        (hB' x).trans (mul_le_mul_of_nonneg_left hAx hc'0)
      exact mul_le_mul_of_nonneg_right hbx (norm_nonneg _)
    have hvv : ⟪v, v⟫ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_num
    have : ‖v‖ ^ 2 ≤ ε * ‖v‖ + c' * (‖v‖ + ε) * ‖v‖ := by
      have hsum : ((‖v‖ ^ 2 : ℝ) : ℂ) = -⟪A x - v, v⟫ - ⟪B x, v⟫ := by
        rw [← hvv]
        have := h0
        rw [e1] at this
        linear_combination this
      have hnorm : (‖v‖ ^ 2 : ℝ) = ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖v‖ ^ 2 = ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ := hnorm
        _ = ‖-⟪A x - v, v⟫ - ⟪B x, v⟫‖ := by rw [hsum]
        _ ≤ ‖(-⟪A x - v, v⟫ : ℂ)‖ + ‖(⟪B x, v⟫ : ℂ)‖ := norm_sub_le _ _
        _ ≤ ε * ‖v‖ + c' * (‖v‖ + ε) * ‖v‖ := by
            rw [norm_neg]; exact add_le_add hb1 hb2
    nlinarith
  have : (1 - c') * ‖v‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h2 : 0 < ε / (1 + c') := by positivity
    have := main (ε / (1 + c')) h2
    have hpos : (0 : ℝ) < 1 + c' := by linarith
    calc (1 - c') * ‖v‖ ≤ ε / (1 + c') * (1 + c') := this
      _ = ε := by field_simp
      _ = 0 + ε := by ring
  nlinarith

/-- If the range of `T + i b` is dense and `|b' - b| < |b|`, then the range of `T + i b'` is
dense as well. -/
theorem dense_range_shift_of_dense_range_shift {ι T : D →ₗ[ℂ] H} (hsym : IsSymmetricOn ι T)
    {b b' : ℝ} (hb : 0 < |b|) (hbb : |b' - b| < |b|)
    (h : Dense (Set.range fun x => T x + ((b : ℂ) * Complex.I) • ι x)) :
    Dense (Set.range fun x => T x + ((b' : ℂ) * Complex.I) • ι x) := by
  set A : D →ₗ[ℂ] H := shift ι T b with hA
  set B : D →ₗ[ℂ] H := (((b' - b : ℝ) : ℂ) * Complex.I) • ι with hBdef
  have hAdense : Dense (Set.range A) := h
  have hbound : ∀ x, ‖B x‖ ≤ (|b' - b| / |b|) * ‖A x‖ := by
    intro x
    have h1 : ‖B x‖ = |b' - b| * ‖ι x‖ := by
      simp only [hBdef, LinearMap.smul_apply, norm_smul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
    have h2 : |b| * ‖ι x‖ ≤ ‖A x‖ := norm_add_I_smul_lower_bound hsym b x
    rw [h1]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    have h3 : |b| * ‖ι x‖ ≤ ‖A x‖ := h2
    calc |b' - b| * ‖ι x‖ * |b| = |b' - b| * (|b| * ‖ι x‖) := by ring
      _ ≤ |b' - b| * ‖A x‖ := by
          exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have hc : |b' - b| / |b| < 1 := by
    rw [div_lt_one hb]; exact hbb
  have hdense := dense_range_add_of_relatively_bounded A B hc hbound hAdense
  have hEq : (fun x => A x + B x) = fun x => T x + ((b' : ℂ) * Complex.I) • ι x := by
    funext x
    simp only [hA, hBdef, shift_apply, LinearMap.smul_apply, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring
  rwa [hEq] at hdense

end Perturbation

/-!
### The closure of an essentially self-adjoint operator is self-adjoint

This section justifies the name `IsEssentiallySelfAdjoint`: if the criterion holds, then the
closure of the graph of `T` coincides with the graph of its adjoint, i.e. the closure of `T` is
a self-adjoint operator.
-/

section GraphClosure

/-- The graph of the operator `(ι, T)`, as a submodule of `H × H`. -/
def opGraph (ι T : D →ₗ[ℂ] H) : Submodule ℂ (H × H) := LinearMap.range (ι.prod T)

lemma mem_opGraph {ι T : D →ₗ[ℂ] H} {p : H × H} :
    p ∈ opGraph ι T ↔ ∃ x, (ι x, T x) = p := Iff.rfl

/-- The adjoint of a linear relation `G ⊆ H × H`: the set of pairs `(v, w)` such that
`⟪q₂, v⟫ = ⟪q₁, w⟫` for all `(q₁, q₂) ∈ G`.  For `G` the graph of an operator `S` this is
exactly the graph of the adjoint `S*`. -/
def graphAdjoint (G : Set (H × H)) : Submodule ℂ (H × H) where
  carrier := {p | ∀ q ∈ G, ⟪q.2, p.1⟫ = ⟪q.1, p.2⟫}
  add_mem' := by
    intro p p' hp hp' q hq
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, hp q hq, hp' q hq]
  zero_mem' := by intro q _; simp
  smul_mem' := by
    intro c p hp q hq
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, hp q hq]

lemma mem_graphAdjoint {G : Set (H × H)} {p : H × H} :
    p ∈ graphAdjoint G ↔ ∀ q ∈ G, ⟪q.2, p.1⟫ = ⟪q.1, p.2⟫ := Iff.rfl

lemma isClosed_graphAdjoint (G : Set (H × H)) :
    IsClosed ((graphAdjoint G : Submodule ℂ (H × H)) : Set (H × H)) := by
  have : ((graphAdjoint G : Submodule ℂ (H × H)) : Set (H × H))
      = ⋂ q ∈ G, {p : H × H | ⟪q.2, p.1⟫ = ⟪q.1, p.2⟫} := by
    ext p; simp [mem_graphAdjoint, Set.mem_iInter]
  rw [this]
  refine isClosed_biInter fun q _ => isClosed_eq ?_ ?_
  · exact continuous_inner.comp (Continuous.prodMk continuous_const continuous_fst)
  · exact continuous_inner.comp (Continuous.prodMk continuous_const continuous_snd)

/-- Passing to the closure does not change the adjoint of a linear relation. -/
theorem graphAdjoint_closure (G : Set (H × H)) : graphAdjoint (closure G) = graphAdjoint G := by
  refine le_antisymm (fun p hp q hq => hp q (subset_closure hq)) ?_
  intro p hp q hq
  have hclosed : IsClosed {q : H × H | ⟪q.2, p.1⟫ = ⟪q.1, p.2⟫} := by
    refine isClosed_eq ?_ ?_
    · exact continuous_inner.comp (Continuous.prodMk continuous_snd continuous_const)
    · exact continuous_inner.comp (Continuous.prodMk continuous_fst continuous_const)
  exact hclosed.closure_subset_iff.2 (fun q hq => hp q hq) hq

variable {ι T : D →ₗ[ℂ] H}

lemma opGraph_le_graphAdjoint (hsym : IsSymmetricOn ι T) :
    (opGraph ι T : Set (H × H)) ⊆ (graphAdjoint (opGraph ι T : Set (H × H)) : Set (H × H)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact (hsym y x).symm ▸ rfl

/-- The basic lower bound on the graph: `‖p‖ ≤ ‖p.2 - i p.1‖`. -/
lemma norm_le_norm_sub_I_smul_of_mem_closure (hsym : IsSymmetricOn ι T) {p : H × H}
    (hp : p ∈ closure (opGraph ι T : Set (H × H))) : ‖p‖ ≤ ‖p.2 - Complex.I • p.1‖ := by
  have hclosed : IsClosed {p : H × H | ‖p‖ ≤ ‖p.2 - Complex.I • p.1‖} := by
    refine isClosed_le continuous_norm ?_
    exact (continuous_snd.sub (continuous_const.smul continuous_fst)).norm
  refine hclosed.closure_subset_iff.2 ?_ hp
  rintro _ ⟨x, rfl⟩
  show ‖((ι x, T x) : H × H)‖ ≤ ‖T x - Complex.I • ι x‖
  have hpyth : ‖T x + (((-1 : ℝ) : ℂ) * Complex.I) • ι x‖ ^ 2 = ‖T x‖ ^ 2 + ‖ι x‖ ^ 2 := by
    rw [norm_add_I_smul_sq hsym (-1) x]; ring
  have hrw : T x + (((-1 : ℝ) : ℂ) * Complex.I) • ι x = T x - Complex.I • ι x := by
    push_cast
    rw [neg_one_mul, neg_smul]
    abel
  rw [hrw] at hpyth
  have hmax : ‖((ι x, T x) : H × H)‖ = max ‖ι x‖ ‖T x‖ := rfl
  have h1 : ‖((ι x, T x) : H × H)‖ ^ 2 ≤ ‖T x - Complex.I • ι x‖ ^ 2 := by
    rw [hpyth, hmax]
    rcases max_cases ‖ι x‖ ‖T x‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [norm_nonneg (ι x), norm_nonneg (T x)]
  have h2 : (0 : ℝ) ≤ ‖T x - Complex.I • ι x‖ := norm_nonneg _
  nlinarith [norm_nonneg ((ι x, T x) : H × H)]

variable [CompleteSpace H]

/-- Every `h : H` is of the form `w - i v` with `(v, w)` in the closure of the graph.  This is
the key surjectivity statement behind von Neumann's criterion. -/
theorem exists_mem_closure_opGraph (h : IsEssentiallySelfAdjoint ι T) (y : H) :
    ∃ p ∈ closure (opGraph ι T : Set (H × H)), p.2 - Complex.I • p.1 = y := by
  set C : Submodule ℂ (H × H) := (opGraph ι T).topologicalClosure with hC
  have hCset : (C : Set (H × H)) = closure (opGraph ι T : Set (H × H)) := rfl
  have hCclosed : IsClosed (C : Set (H × H)) := (opGraph ι T).isClosed_topologicalClosure
  haveI : CompleteSpace C := hCclosed.completeSpace_coe
  set fmap : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) - Complex.I • (ContinuousLinearMap.fst ℂ H H) with hfmap
  set f : C →L[ℂ] H := fmap.comp C.subtypeL with hf
  have hbound : ∀ p : C, ‖(p : H × H)‖ ≤ ‖f p‖ := by
    intro p
    have := norm_le_norm_sub_I_smul_of_mem_closure h.symmetric (p := (p : H × H)) p.2
    simpa [hf, hfmap] using this
  have hanti : AntilipschitzWith 1 f := by
    refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
    have hpq : ‖(p : H × H) - (q : H × H)‖ ≤ ‖f (p - q)‖ := hbound (p - q)
    simpa [dist_eq_norm, map_sub] using hpq
  have hclosedRange : IsClosed (Set.range f) := hanti.isClosed_range f.uniformContinuous
  have hdenseRange : Dense (Set.range f) := by
    refine Dense.mono ?_ h.dense_range_sub_I
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨(ι x, T x), ?_⟩, ?_⟩
    · exact subset_closure ⟨x, rfl⟩
    · simp [hf, hfmap]
  have hall : Set.range f = Set.univ := hclosedRange.closure_eq ▸ hdenseRange.closure_eq
  obtain ⟨p, hp⟩ : ∃ p : C, f p = y := by
    have : y ∈ Set.range f := by rw [hall]; trivial
    exact this
  exact ⟨(p : H × H), p.2, by simpa [hf, hfmap] using hp⟩

/-- **The closure of an essentially self-adjoint operator is self-adjoint.**  If `(ι, T)`
satisfies von Neumann's criterion, the closure of its graph is equal to its own adjoint. -/
theorem graphAdjoint_closure_opGraph (h : IsEssentiallySelfAdjoint ι T) :
    (graphAdjoint (closure (opGraph ι T : Set (H × H))) : Set (H × H))
      = closure (opGraph ι T : Set (H × H)) := by
  rw [graphAdjoint_closure]
  refine le_antisymm ?_ ?_
  · -- the hard inclusion: the adjoint is contained in the closure of the graph
    intro p hp
    obtain ⟨p₀, hp₀mem, hp₀⟩ := exists_mem_closure_opGraph h (p.2 - Complex.I • p.1)
    have hp₀adj : p₀ ∈ graphAdjoint (opGraph ι T : Set (H × H)) := by
      have hsub : closure (opGraph ι T : Set (H × H))
          ⊆ (graphAdjoint (opGraph ι T : Set (H × H)) : Set (H × H)) :=
        (isClosed_graphAdjoint _).closure_subset_iff.2 (opGraph_le_graphAdjoint h.symmetric)
      exact hsub hp₀mem
    set u : H := p.1 - p₀.1 with hu
    have hw : p.2 - p₀.2 = Complex.I • u := by
      have := hp₀
      rw [hu, smul_sub]
      linear_combination (norm := module) -this
    have hudef : ∀ x, ⟪T x, u⟫ = Complex.I * ⟪ι x, u⟫ := by
      intro x
      have h1 : ⟪T x, p.1⟫ = ⟪ι x, p.2⟫ := hp (ι x, T x) ⟨x, rfl⟩
      have h2 : ⟪T x, p₀.1⟫ = ⟪ι x, p₀.2⟫ := hp₀adj (ι x, T x) ⟨x, rfl⟩
      have h3 : ⟪T x, u⟫ = ⟪ι x, p.2 - p₀.2⟫ := by
        rw [hu, inner_sub_right, inner_sub_right, h1, h2]
      rw [h3, hw, inner_smul_right]
    have hu0 : u = 0 := by
      have hkey := (dense_range_iff_forall_inner_eq_zero (T + Complex.I • ι)).1 ?_ u ?_
      · exact hkey
      · have := h.dense_range_add_I
        simpa [show (fun x => T x + Complex.I • ι x) = ⇑(T + Complex.I • ι) from rfl] using this
      · intro x
        simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
          hudef x]
        simp [Complex.conj_I]
    have hp1 : p.1 = p₀.1 := by
      rw [hu] at hu0
      exact sub_eq_zero.mp hu0
    have hp2 : p.2 = p₀.2 := by
      have hz : p.2 - p₀.2 = 0 := by rw [hw, hu0, smul_zero]
      exact sub_eq_zero.mp hz
    have hpp : p = p₀ := Prod.ext hp1 hp2
    rw [hpp]
    exact hp₀mem
  · exact (isClosed_graphAdjoint _).closure_subset_iff.2 (opGraph_le_graphAdjoint h.symmetric)

end GraphClosure

end Brockian.Weyl

import Brockian.Weyl.FreeSchrodinger

/-!
# Essential self-adjointness of one-dimensional Schrödinger operators

Let `V : ℝ → ℝ` be a potential which is only assumed to be *weakly regular*, i.e. measurable and
essentially bounded (`MemLp V ⊤`); no continuity or differentiability is assumed.  The associated
Schrödinger operator

`H u = - u'' + V u`

with domain the Schwartz space `𝓢(ℝ, ℂ) ⊆ L²(ℝ)` is then essentially self-adjoint, in the sense
of `Brockian.Weyl.IsEssentiallySelfAdjoint` (von Neumann's basic criterion: `H` is symmetric,
densely defined, and the ranges of `H ± i` are dense).

The proof combines two ingredients:

* the Fourier-analytic solution of the free deficiency ODE `-u'' + i b u = f`
  (`Brockian.Weyl.dense_range_freeOp_shift`), which shows that the free operator `-d²/dx²`
  has trivial deficiency spaces;
* the Kato–Rellich perturbation argument (`Brockian.Weyl.dense_range_add_of_relatively_bounded`):
  for `|b|` larger than the essential supremum of `|V|`, the multiplication operator `V` is a
  relatively bounded perturbation of `-d²/dx² + i b` with relative bound `< 1`, and density of
  the range is then transported back to the spectral parameters `± i`.

Main result: `Brockian.Weyl.schrodinger_essentiallySelfAdjoint_of_weakRegularity`.
-/

noncomputable section

open MeasureTheory SchwartzMap Complex Real
open scoped FourierTransform ComplexInnerProductSpace ContDiff

namespace Brockian.Weyl

/-! ### The potential as a bounded multiplication operator on `L²` -/

/-- A real-valued potential, complexified. -/
abbrev cx (V : ℝ → ℝ) : ℝ → ℂ := fun x => (V x : ℂ)

/-- Multiplication by an essentially bounded potential, as an operator on `L²(ℝ)`. -/
def mulPotential (V : ℝ → ℝ) (hV : MemLp (cx V) ⊤ volume) : L2R →ₗ[ℂ] L2R :=
  ContinuousLinearMap.holderₗ volume ⊤ 2 2 (ContinuousLinearMap.mul ℂ ℂ) hV.toLp

lemma coeFn_mulPotential {V : ℝ → ℝ} (hV : MemLp (cx V) ⊤ volume) (f : L2R) :
    (mulPotential V hV f : ℝ → ℂ) =ᵐ[volume] fun x => (V x : ℂ) * f x := by
  have hmul : mulPotential V hV f
      = ContinuousLinearMap.holder 2 (ContinuousLinearMap.mul ℂ ℂ) hV.toLp f := rfl
  rw [hmul]
  have h1 := ContinuousLinearMap.coeFn_holder (μ := volume) (p := ⊤) (q := 2) (r := 2)
    (ContinuousLinearMap.mul ℂ ℂ) hV.toLp f
  have h2 := hV.coeFn_toLp
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  simp [hx2]

/-- An essentially bounded function admits a nonnegative almost-everywhere bound. -/
lemma exists_bound_of_memLp_top {f : ℝ → ℂ} (hf : MemLp f ⊤ volume) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x, ‖f x‖ ≤ M := by
  refine ⟨(eLpNormEssSup f volume).toReal, ENNReal.toReal_nonneg, ?_⟩
  have h1 : eLpNormEssSup f volume ≠ ⊤ := by
    have h := hf.eLpNorm_lt_top
    rw [eLpNorm_exponent_top] at h
    exact h.ne
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with x hx
  have h2 : (‖f x‖ₑ).toReal ≤ (eLpNormEssSup f volume).toReal := ENNReal.toReal_mono h1 hx
  simpa using h2

lemma norm_mulPotential_le {V : ℝ → ℝ} (hV : MemLp (cx V) ⊤ volume) {M : ℝ}
    (hM : ∀ᵐ x, ‖(V x : ℂ)‖ ≤ M) (f : L2R) : ‖mulPotential V hV f‖ ≤ M * ‖f‖ := by
  refine MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_mulPotential hV f, hM] with x hx hMx
  rw [hx]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hMx (norm_nonneg _)

/-- Multiplication by a real potential is a symmetric operator. -/
lemma inner_mulPotential {V : ℝ → ℝ} (hV : MemLp (cx V) ⊤ volume) (f g : L2R) :
    ⟪mulPotential V hV f, g⟫ = ⟪f, mulPotential V hV g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulPotential hV f, coeFn_mulPotential hV g] with x hx hy
  rw [hx, hy, RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ### The Schrödinger operator -/

/-- The Schrödinger operator `u ↦ -u'' + V u` with domain the Schwartz space, as an operator
into `L²(ℝ)`. -/
def schrodingerOp (V : ℝ → ℝ) (hV : MemLp (cx V) ⊤ volume) : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R :=
  freeOp + (mulPotential V hV) ∘ₗ iotaS

@[simp] lemma schrodingerOp_apply (V : ℝ → ℝ) (hV : MemLp (cx V) ⊤ volume) (φ : 𝓢(ℝ, ℂ)) :
    schrodingerOp V hV φ = freeOp φ + mulPotential V hV (iotaS φ) := rfl

/-- The Schrödinger operator is symmetric on the Schwartz space. -/
theorem schrodingerOp_symmetric (V : ℝ → ℝ) (hV : MemLp (cx V) ⊤ volume) :
    IsSymmetricOn iotaS (schrodingerOp V hV) := by
  intro φ ψ
  rw [schrodingerOp_apply, schrodingerOp_apply, inner_add_left, inner_add_right,
    freeOp_symmetric φ ψ, inner_mulPotential hV (iotaS φ) (iotaS ψ)]

/-- Density of the range of `H + i b` for a large spectral parameter `b`: this is the
Kato–Rellich perturbation step. -/
theorem dense_range_schrodinger_shift_of_large {V : ℝ → ℝ} (hV : MemLp (cx V) ⊤ volume)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x, ‖(V x : ℂ)‖ ≤ M) {b : ℝ} (hb : M < |b|) :
    Dense (Set.range fun φ : 𝓢(ℝ, ℂ) => schrodingerOp V hV φ + ((b : ℂ) * I) • iotaS φ) := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
    linarith
  set A : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R := shift iotaS freeOp b with hA
  set B : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R := (mulPotential V hV) ∘ₗ iotaS with hB
  have hAdense : Dense (Set.range A) := dense_range_freeOp_shift hbne
  have habs : 0 < |b| := lt_of_le_of_lt hM0 hb
  have hbound : ∀ φ, ‖B φ‖ ≤ (M / |b|) * ‖A φ‖ := by
    intro φ
    have h1 : ‖B φ‖ ≤ M * ‖iotaS φ‖ := norm_mulPotential_le hV hM (iotaS φ)
    have h2 : |b| * ‖iotaS φ‖ ≤ ‖A φ‖ := norm_add_I_smul_lower_bound freeOp_symmetric b φ
    rw [div_mul_eq_mul_div, le_div_iff₀ habs]
    calc ‖B φ‖ * |b| ≤ (M * ‖iotaS φ‖) * |b| := by
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt habs)
      _ = M * (|b| * ‖iotaS φ‖) := by ring
      _ ≤ M * ‖A φ‖ := mul_le_mul_of_nonneg_left h2 hM0
  have hc : M / |b| < 1 := (div_lt_one habs).2 hb
  have hdense := dense_range_add_of_relatively_bounded A B hc hbound hAdense
  have hEq : (fun φ => A φ + B φ)
      = fun φ : 𝓢(ℝ, ℂ) => schrodingerOp V hV φ + ((b : ℂ) * I) • iotaS φ := by
    funext φ
    simp only [hA, hB, shift_apply, LinearMap.coe_comp, Function.comp_apply,
      schrodingerOp_apply]
    abel
  rwa [hEq] at hdense

/-- **Essential self-adjointness of the Schrödinger operator `-d²/dx² + V` under weak
regularity of the potential.**

If the real potential `V` is measurable and essentially bounded (`MemLp (fun x ↦ (V x : ℂ)) ⊤`,
which is exactly the *weak regularity* assumption: no smoothness whatsoever is required), then
the operator `u ↦ -u'' + V u`, with domain the Schwartz space `𝓢(ℝ, ℂ)` inside `L²(ℝ)`, is
essentially self-adjoint. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity (V : ℝ → ℝ)
    (hV : MemLp (cx V) ⊤ volume) :
    IsEssentiallySelfAdjoint iotaS (schrodingerOp V hV) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_memLp_top hV
  set b : ℝ := M + 1 with hbdef
  have hbabs : |b| = b := abs_of_pos (by linarith)
  have hMb : M < |b| := by rw [hbabs]; linarith
  have hsym := schrodingerOp_symmetric V hV
  have hplus := dense_range_schrodinger_shift_of_large hV hM0 hM hMb
  have hminus : Dense (Set.range fun φ : 𝓢(ℝ, ℂ) =>
      schrodingerOp V hV φ + (((-b : ℝ) : ℂ) * I) • iotaS φ) := by
    refine dense_range_schrodinger_shift_of_large hV hM0 hM ?_
    rw [abs_neg, hbabs]
    linarith
  refine ⟨dense_range_iotaS, hsym, ?_, ?_⟩
  · have h1 : Dense (Set.range fun φ : 𝓢(ℝ, ℂ) =>
        schrodingerOp V hV φ + (((1 : ℝ) : ℂ) * I) • iotaS φ) := by
      refine dense_range_shift_of_dense_range_shift hsym (b := b) ?_ ?_ hplus
      · rw [hbabs]; linarith
      · rw [hbabs, abs_lt]; constructor <;> linarith
    simpa using h1
  · have h1 : Dense (Set.range fun φ : 𝓢(ℝ, ℂ) =>
        schrodingerOp V hV φ + (((-1 : ℝ) : ℂ) * I) • iotaS φ) := by
      refine dense_range_shift_of_dense_range_shift hsym (b := -b) ?_ ?_ hminus
      · rw [abs_neg, hbabs]; linarith
      · rw [abs_neg, hbabs, abs_lt]; constructor <;> linarith
    have h2 : (fun φ : 𝓢(ℝ, ℂ) => schrodingerOp V hV φ + (((-1 : ℝ) : ℂ) * I) • iotaS φ)
        = fun φ : 𝓢(ℝ, ℂ) => schrodingerOp V hV φ - I • iotaS φ := by
      funext φ
      push_cast
      rw [neg_one_mul, neg_smul]
      abel
    rwa [h2] at h1

/-- The closure of the Schrödinger operator `u ↦ -u'' + V u` is a self-adjoint operator: the
closure of its graph coincides with the graph of its adjoint.  This is the unbundled form of
`schrodinger_essentiallySelfAdjoint_of_weakRegularity`. -/
theorem schrodinger_closure_selfAdjoint (V : ℝ → ℝ) (hV : MemLp (cx V) ⊤ volume) :
    (graphAdjoint (closure (opGraph iotaS (schrodingerOp V hV) : Set (L2R × L2R)))
        : Set (L2R × L2R))
      = closure (opGraph iotaS (schrodingerOp V hV) : Set (L2R × L2R)) :=
  graphAdjoint_closure_opGraph (schrodinger_essentiallySelfAdjoint_of_weakRegularity V hV)

/-- The weak regularity hypothesis is satisfiable: the zero potential satisfies it, so the main
theorem is not vacuous. -/
theorem memLp_top_cx_zero : MemLp (cx (fun _ : ℝ => (0 : ℝ))) ⊤ volume := by
  have hfun : cx (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => (0 : ℂ) := by
    funext x
    simp [cx]
  rw [hfun]
  exact memLp_top_const 0

end Brockian.Weyl

import Brockian.Weyl.Operator

/-!
# The free Schrödinger operator `-d²/dx²` on the Schwartz space

We realise `H₀ = -d²/dx²` as an operator in `L²(ℝ)` with domain the Schwartz space `𝓢(ℝ, ℂ)`,
and prove that it is symmetric with densely defined domain and that the ranges of `H₀ + i b`
are dense for every real `b ≠ 0`.

The proof of density is the Fourier-analytic solution of the *deficiency ODE*
`-u'' + i b u = f`: on the Fourier side the equation becomes multiplication by
`4 π² ξ² + i b`, a function which never vanishes when `b ≠ 0`, so that every smooth compactly
supported function is exactly attained; those are dense in `L²`.
-/

noncomputable section

open MeasureTheory SchwartzMap Complex Real
open scoped FourierTransform ComplexInnerProductSpace ContDiff

namespace Brockian.Weyl

/-- The Hilbert space `L²(ℝ, ℂ)`. -/
abbrev L2R : Type := Lp (α := ℝ) ℂ 2 volume

/-- The Schwartz space, viewed inside `L²(ℝ)`. -/
def iotaS : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R := (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

@[simp] lemma iotaS_apply (φ : 𝓢(ℝ, ℂ)) : iotaS φ = φ.toLp 2 volume := rfl

/-- Minus the second derivative, as an operator on the Schwartz space. -/
def negD2 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := -(derivCLM ℂ ℂ ∘L derivCLM ℂ ℂ)

/-- The free Schrödinger operator `-d²/dx²` with domain `𝓢(ℝ, ℂ)`, as an operator into
`L²(ℝ)`. -/
def freeOp : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R := iotaS ∘ₗ (negD2 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)).toLinearMap

@[simp] lemma freeOp_apply (φ : 𝓢(ℝ, ℂ)) : freeOp φ = iotaS (negD2 φ) := rfl

/-- The domain of the free Schrödinger operator is dense in `L²(ℝ)`. -/
theorem dense_range_iotaS : Dense (Set.range iotaS) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume)
    (by simp)
  have hrange : Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 volume) = Set.range iotaS := by
    ext v; constructor <;> rintro ⟨φ, rfl⟩ <;> exact ⟨φ, rfl⟩
  rw [DenseRange, hrange] at h
  exact h

/-! ### Fourier transform of the free operator -/

lemma deriv_coe_schwartz (φ : 𝓢(ℝ, ℂ)) : (deriv (⇑φ) : ℝ → ℂ) = ⇑(derivCLM ℂ ℂ φ) := by
  ext x; simp [SchwartzMap.derivCLM_apply]

lemma integrable_deriv_schwartz (φ : 𝓢(ℝ, ℂ)) : Integrable (deriv (⇑φ)) volume := by
  rw [deriv_coe_schwartz]; exact (derivCLM ℂ ℂ φ).integrable

lemma fourier_deriv_deriv (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (deriv (deriv (⇑φ))) ξ = -(4 * π ^ 2 * ξ ^ 2) * 𝓕 (⇑φ) ξ := by
  have step1 : 𝓕 (deriv (⇑φ)) = fun x : ℝ => (2 * π * I * x) • 𝓕 (⇑φ) x :=
    Real.fourier_deriv φ.integrable φ.differentiable (integrable_deriv_schwartz φ)
  have step2 : 𝓕 (deriv (deriv (⇑φ))) = fun x : ℝ => (2 * π * I * x) • 𝓕 (deriv (⇑φ)) x := by
    rw [deriv_coe_schwartz]
    exact Real.fourier_deriv (derivCLM ℂ ℂ φ).integrable (derivCLM ℂ ℂ φ).differentiable
      (integrable_deriv_schwartz (derivCLM ℂ ℂ φ))
  rw [congrFun step2 ξ, congrFun step1 ξ]
  simp only [smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

lemma coe_negD2 (φ : 𝓢(ℝ, ℂ)) : ⇑(negD2 φ) = fun x => -(deriv (deriv (⇑φ)) x) := by
  ext x
  simp only [negD2, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.neg_apply, SchwartzMap.derivCLM_apply]
  rw [← deriv_coe_schwartz]

/-- On the Fourier side the free Schrödinger operator is multiplication by `4 π² ξ²`. -/
lemma fourier_negD2_apply (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (negD2 φ) : 𝓢(ℝ, ℂ)) ξ = ((4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, coe_negD2]
  have hneg : 𝓕 (fun x => -(deriv (deriv (⇑φ)) x)) ξ = -𝓕 (deriv (deriv (⇑φ))) ξ := by
    simp only [Real.fourier_eq, ← integral_neg]
    congr 1
    ext x
    simp
  rw [hneg, fourier_deriv_deriv]
  push_cast
  ring

/-! ### Symmetry of the free operator -/

lemma inner_iotaS (u v : 𝓢(ℝ, ℂ)) :
    ⟪iotaS u, iotaS v⟫ = ∫ x : ℝ, (starRingEnd ℂ) (u x) * v x := by
  rw [iotaS_apply, iotaS_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [u.coeFn_toLp 2 volume, v.coeFn_toLp 2 volume] with x hu hv
  rw [hu, hv, RCLike.inner_apply]
  ring

lemma fourier_iotaS (u : 𝓢(ℝ, ℂ)) : 𝓕 (iotaS u) = iotaS (𝓕 u : 𝓢(ℝ, ℂ)) := by
  simp [SchwartzMap.toLp_fourier_eq]

lemma inner_freeOp_iotaS (φ ψ : 𝓢(ℝ, ℂ)) :
    ⟪freeOp φ, iotaS ψ⟫ = ∫ ξ : ℝ, ((4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ) ((𝓕 φ : 𝓢(ℝ, ℂ)) ξ) * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := by
  have e1 : ⟪freeOp φ, iotaS ψ⟫
      = ⟪iotaS (𝓕 (negD2 φ) : 𝓢(ℝ, ℂ)), iotaS (𝓕 ψ : 𝓢(ℝ, ℂ))⟫ := by
    rw [← fourier_iotaS, ← fourier_iotaS, MeasureTheory.Lp.inner_fourier_eq]
    rfl
  rw [e1, inner_iotaS]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [fourier_negD2_apply]
  rw [map_mul, Complex.conj_ofReal]
  ring

lemma inner_iotaS_freeOp (φ ψ : 𝓢(ℝ, ℂ)) :
    ⟪iotaS φ, freeOp ψ⟫ = ∫ ξ : ℝ, ((4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) *
      ((starRingEnd ℂ) ((𝓕 φ : 𝓢(ℝ, ℂ)) ξ) * (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := by
  have e1 : ⟪iotaS φ, freeOp ψ⟫
      = ⟪iotaS (𝓕 φ : 𝓢(ℝ, ℂ)), iotaS (𝓕 (negD2 ψ) : 𝓢(ℝ, ℂ))⟫ := by
    rw [← fourier_iotaS, ← fourier_iotaS, MeasureTheory.Lp.inner_fourier_eq]
    rfl
  rw [e1, inner_iotaS]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [fourier_negD2_apply]
  ring

/-- The free Schrödinger operator is symmetric. -/
theorem freeOp_symmetric : IsSymmetricOn iotaS freeOp := fun φ ψ => by
  rw [inner_freeOp_iotaS, inner_iotaS_freeOp]

/-! ### Density of the ranges of `H₀ + i b` -/

/-- The symbol of `-d²/dx² + i b` on the Fourier side. -/
def freeSymbol (b : ℝ) (ξ : ℝ) : ℂ := ((4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) + (b : ℂ) * I

lemma freeSymbol_ne_zero {b : ℝ} (hb : b ≠ 0) (ξ : ℝ) : freeSymbol b ξ ≠ 0 := by
  have him : (freeSymbol b ξ).im = b := by
    simp only [freeSymbol, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, Complex.ofReal_re]
    ring
  intro h
  apply hb
  rw [← him, h, Complex.zero_im]

lemma contDiff_freeSymbol (b : ℝ) : ContDiff ℝ ∞ (freeSymbol b) := by
  have h1 : ContDiff ℝ ∞ fun ξ : ℝ => ((4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_id.pow 2))
  exact h1.add contDiff_const

lemma contDiff_inv_freeSymbol {b : ℝ} (hb : b ≠ 0) :
    ContDiff ℝ ∞ (fun ξ : ℝ => (freeSymbol b ξ)⁻¹) :=
  (contDiff_freeSymbol b).inv (freeSymbol_ne_zero hb)

/-- Solvability of the deficiency ODE `-u'' + i b u = f` for smooth compactly supported `f`,
with `u` a Schwartz function: on the Fourier side one divides by the non-vanishing symbol. -/
lemma exists_schwartz_solution {b : ℝ} (hb : b ≠ 0) (g : 𝓢(ℝ, ℂ)) (hg : HasCompactSupport ⇑g) :
    ∃ φ : 𝓢(ℝ, ℂ),
      (𝓕 (negD2 φ) : 𝓢(ℝ, ℂ)) + ((b : ℂ) * I) • (𝓕 φ : 𝓢(ℝ, ℂ)) = g := by
  have hw_cs : HasCompactSupport (fun ξ : ℝ => g ξ * (freeSymbol b ξ)⁻¹) :=
    HasCompactSupport.mul_right (f' := fun ξ : ℝ => (freeSymbol b ξ)⁻¹) hg
  have hw_sm : ContDiff ℝ ∞ (fun ξ : ℝ => g ξ * (freeSymbol b ξ)⁻¹) :=
    g.smooth'.mul (contDiff_inv_freeSymbol hb)
  set ψ : 𝓢(ℝ, ℂ) := hw_cs.toSchwartzMap hw_sm with hψ
  refine ⟨𝓕⁻ ψ, ?_⟩
  have hF : (𝓕 (𝓕⁻ ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = ψ := FourierTransform.fourier_fourierInv_eq ψ
  ext ξ
  rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, fourier_negD2_apply, hF]
  have hψξ : ψ ξ = g ξ * (freeSymbol b ξ)⁻¹ := rfl
  rw [hψξ, smul_eq_mul]
  have hne : ((4 * π ^ 2 * ξ ^ 2 : ℝ) : ℂ) + (b : ℂ) * I ≠ 0 := freeSymbol_ne_zero hb ξ
  simp only [freeSymbol]
  field_simp

/-- **The deficiency spaces of the free Schrödinger operator are trivial**: the range of
`-d²/dx² + i b` on the Schwartz space is dense in `L²(ℝ)` for every real `b ≠ 0`. -/
theorem dense_range_freeOp_shift {b : ℝ} (hb : b ≠ 0) :
    Dense (Set.range fun φ : 𝓢(ℝ, ℂ) => freeOp φ + ((b : ℂ) * I) • iotaS φ) := by
  set e : L2R ≃ₗᵢ[ℂ] L2R := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ with he
  have hcoe : ∀ f : L2R, e f = 𝓕 f := fun _ => rfl
  have key : ∀ φ : 𝓢(ℝ, ℂ), e (freeOp φ + ((b : ℂ) * I) • iotaS φ)
      = iotaS ((𝓕 (negD2 φ) : 𝓢(ℝ, ℂ)) + ((b : ℂ) * I) • (𝓕 φ : 𝓢(ℝ, ℂ))) := by
    intro φ
    rw [map_add, map_smul, hcoe, hcoe, freeOp_apply, fourier_iotaS, fourier_iotaS,
      map_add, map_smul]
  suffices hd : Dense (Set.range fun φ : 𝓢(ℝ, ℂ) =>
      e (freeOp φ + ((b : ℂ) * I) • iotaS φ)) by
    have h1 : DenseRange (⇑e.symm) := e.symm.surjective.denseRange
    have h2 := h1.comp hd e.symm.continuous
    simpa [Function.comp_def] using h2
  simp only [key]
  intro v
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le (p := 2)
    (by simp) (by norm_num) (MeasureTheory.Lp.memLp v) hε
  set gS : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hgS
  have hgScs : HasCompactSupport (⇑gS) := hg₁
  obtain ⟨φ, hφ⟩ := exists_schwartz_solution hb gS hgScs
  refine ⟨iotaS gS, ⟨φ, congrArg iotaS hφ⟩, ?_⟩
  have hae : (v : ℝ → ℂ) - ((iotaS gS : L2R) : ℝ → ℂ) =ᵐ[volume] (v : ℝ → ℂ) - g := by
    filter_upwards [gS.coeFn_toLp 2 volume] with x hx
    have hgx : ((gS.toLp 2 volume : L2R) : ℝ → ℂ) x = g x := hx
    simp [hgx]
  simp only [Metric.mem_closedBall', MeasureTheory.Lp.dist_def,
    MeasureTheory.eLpNorm_congr_ae hae]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  exact ENNReal.ofReal_ne_top

/-- **The free Schrödinger operator `-d²/dx²` with domain `𝓢(ℝ, ℂ)` is essentially
self-adjoint in `L²(ℝ)`.** -/
theorem freeOp_essentiallySelfAdjoint : IsEssentiallySelfAdjoint iotaS freeOp := by
  refine ⟨dense_range_iotaS, freeOp_symmetric, ?_, ?_⟩
  · have h1 := dense_range_freeOp_shift (b := (1 : ℝ)) one_ne_zero
    simpa using h1
  · have h1 := dense_range_freeOp_shift (b := (-1 : ℝ)) (by norm_num)
    have h2 : (fun φ : 𝓢(ℝ, ℂ) => freeOp φ + (((-1 : ℝ) : ℂ) * I) • iotaS φ)
        = fun φ : 𝓢(ℝ, ℂ) => freeOp φ - I • iotaS φ := by
      funext φ
      push_cast
      rw [neg_one_mul, neg_smul]
      abel
    rwa [h2] at h1

end Brockian.Weyl

