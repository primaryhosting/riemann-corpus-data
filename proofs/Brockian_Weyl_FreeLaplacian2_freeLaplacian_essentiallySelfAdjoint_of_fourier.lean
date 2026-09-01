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
# Graphs of unbounded operators on a Hilbert space

This file develops the small amount of unbounded-operator theory that is needed to state and
prove essential self-adjointness of a densely defined symmetric operator.

An unbounded operator on a complex Hilbert space `H` is encoded by its graph, a linear subspace
`G ≤ H × H` (a *linear relation*).  Its adjoint is the linear relation

`G† = {(y, z) | ∀ (x, w) ∈ G, ⟪w, y⟫ = ⟪x, z⟫}`,

and `G` is *essentially self-adjoint* if it is densely defined, symmetric (`G ≤ G†`) and the
closure of `G` coincides with `G†`; equivalently, the operator has a unique self-adjoint
extension, namely its closure.

The main result is the basic criterion of von Neumann
(`Brockian.Weyl.isEssentiallySelfAdjoint_of_dense_shiftRange`): a densely defined symmetric
operator whose deficiency subspaces are trivial, i.e. for which the ranges of `T + i` and
`T - i` are dense, is essentially self-adjoint.
-/

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The adjoint of a linear relation `G ≤ H × H`.  If `G` is the graph of a densely defined
operator `T`, then this is the graph of the adjoint operator `T†`. -/
def adjointGraph (G : Submodule ℂ (H × H)) : Submodule ℂ (H × H) where
  carrier := {q | ∀ p ∈ G, inner ℂ p.2 q.1 = inner ℂ p.1 q.2}
  add_mem' := by
    intro a b ha hb p hp
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, ha p hp, hb p hp]
  zero_mem' := by intro p _; simp
  smul_mem' := by
    intro c a ha p hp
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, ha p hp]

@[simp]
theorem mem_adjointGraph {G : Submodule ℂ (H × H)} {q : H × H} :
    q ∈ adjointGraph G ↔ ∀ p ∈ G, inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := Iff.rfl

/-- The domain of a linear relation. -/
def domain (G : Submodule ℂ (H × H)) : Submodule ℂ H := G.map (LinearMap.fst ℂ H H)

/-- The range of `T + c`, for a linear relation `G` which is the graph of `T`. -/
def shiftRange (G : Submodule ℂ (H × H)) (c : ℂ) : Submodule ℂ H :=
  G.map (LinearMap.snd ℂ H H + c • LinearMap.fst ℂ H H)

theorem mem_shiftRange {G : Submodule ℂ (H × H)} {c : ℂ} {y : H} :
    y ∈ shiftRange G c ↔ ∃ p ∈ G, p.2 + c • p.1 = y := by
  simp [shiftRange, Submodule.mem_map]

/-- A linear relation `G` is essentially self-adjoint if it is densely defined, symmetric, and
its closure agrees with its adjoint. -/
structure IsEssentiallySelfAdjoint (G : Submodule ℂ (H × H)) : Prop where
  /-- The domain is dense. -/
  dense_domain : Dense (domain G : Set H)
  /-- The operator is symmetric. -/
  symmetric : G ≤ adjointGraph G
  /-- The closure of the operator is its own adjoint; equivalently the closure is self-adjoint. -/
  closure_eq_adjoint : G.topologicalClosure = adjointGraph G

/-- The adjoint relation is closed. -/
theorem isClosed_adjointGraph (G : Submodule ℂ (H × H)) :
    IsClosed (adjointGraph G : Set (H × H)) := by
  have h : (adjointGraph G : Set (H × H)) =
      ⋂ p ∈ (G : Set (H × H)), {q : H × H | inner ℂ p.2 q.1 = inner ℂ p.1 q.2} := by
    ext q; simp [adjointGraph]
  rw [h]
  refine isClosed_biInter fun p _ => ?_
  exact isClosed_eq (by fun_prop) (by fun_prop)

theorem adjointGraph_antitone {G G' : Submodule ℂ (H × H)} (h : G ≤ G') :
    adjointGraph G' ≤ adjointGraph G := fun _ hq p hp => hq p (h hp)

theorem adjointGraph_topologicalClosure (G : Submodule ℂ (H × H)) :
    adjointGraph G.topologicalClosure = adjointGraph G := by
  refine le_antisymm (adjointGraph_antitone G.le_topologicalClosure) ?_
  intro q hq p hp
  have hclosed : IsClosed {p : H × H | inner ℂ p.2 q.1 = inner ℂ p.1 q.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact hclosed.closure_subset_iff.2 (fun r hr => hq r hr) hp

theorem topologicalClosure_le_adjointGraph {G : Submodule ℂ (H × H)}
    (hsym : G ≤ adjointGraph G) : G.topologicalClosure ≤ adjointGraph G := by
  intro p hp
  exact (isClosed_adjointGraph G).closure_subset_iff.2 hsym hp

/-- For a point of a symmetric relation, `⟪w, x⟫` is real. -/
theorem inner_self_swap {G : Submodule ℂ (H × H)} (hsym : G ≤ adjointGraph G) {p : H × H}
    (hp : p ∈ G) : (inner ℂ p.2 p.1 : ℂ) = inner ℂ p.1 p.2 := hsym hp p hp

/-- The Pythagoras identity `‖w + c • x‖² = ‖w‖² + ‖x‖²` for purely imaginary `c` of modulus one
and `(x, w)` a point at which the relation is symmetric. -/
theorem norm_shift_sq {p : H × H} (hp : (inner ℂ p.2 p.1 : ℂ) = inner ℂ p.1 p.2) {c : ℂ}
    (hc : c.re = 0) (hc' : ‖c‖ = 1) :
    ‖p.2 + c • p.1‖ ^ 2 = ‖p.2‖ ^ 2 + ‖p.1‖ ^ 2 := by
  have hreal : (inner ℂ p.2 p.1 : ℂ).im = 0 := by
    have h2 : (inner ℂ p.1 p.2 : ℂ) = starRingEnd ℂ (inner ℂ p.2 p.1) :=
      (inner_conj_symm _ _).symm
    rw [h2] at hp
    have h3 := congrArg Complex.im hp
    simp only [Complex.conj_im] at h3
    linarith
  have hexp : ‖p.2 + c • p.1‖ ^ 2 =
      ‖p.2‖ ^ 2 + 2 * (inner ℂ p.2 (c • p.1) : ℂ).re + ‖c • p.1‖ ^ 2 := by
    simpa using norm_add_sq_real (𝕜 := ℂ) p.2 (c • p.1)
  have hinner : (inner ℂ p.2 (c • p.1) : ℂ) = c * inner ℂ p.2 p.1 := by
    rw [inner_smul_right]
  rw [hexp, hinner, norm_smul, hc']
  simp [Complex.mul_re, hc, hreal]

/-- Triviality of a deficiency space: if the range of `T + c` is dense and `(y, -conj c • y)`
lies in the adjoint, then `y = 0`. -/
theorem eq_zero_of_dense_shiftRange {G : Submodule ℂ (H × H)} {c : ℂ}
    (hdense : Dense (shiftRange G c : Set H)) {y : H}
    (hy : (y, -(starRingEnd ℂ c) • y) ∈ adjointGraph G) : y = 0 := by
  have horth : ∀ v ∈ shiftRange G c, (inner ℂ v y : ℂ) = 0 := by
    intro v hv
    rw [mem_shiftRange] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    have h := hy p hp
    simp only at h
    rw [inner_add_left, inner_smul_left, h, inner_smul_right]
    ring
  have hall : ∀ v : H, (inner ℂ v y : ℂ) = 0 := by
    intro v
    have hclosed : IsClosed {w : H | (inner ℂ w y : ℂ) = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    have hcl : ∀ w ∈ closure (shiftRange G c : Set H), (inner ℂ w y : ℂ) = 0 := fun w hw =>
      hclosed.closure_subset_iff.2 horth hw
    exact hcl v (by rw [hdense.closure_eq]; trivial)
  simpa using inner_self_eq_zero.1 (hall y)

section Complete

variable [CompleteSpace H]

/-- On the closure of a symmetric relation, the map `(x, w) ↦ w + c • x` is surjective as soon
as the range of `T + c` is dense. -/
theorem shiftRange_closure_eq_top {G : Submodule ℂ (H × H)} (hsym : G ≤ adjointGraph G) {c : ℂ}
    (hc : c.re = 0) (hc' : ‖c‖ = 1) (hdense : Dense (shiftRange G c : Set H)) (y : H) :
    ∃ p ∈ G.topologicalClosure, p.2 + c • p.1 = y := by
  set K := G.topologicalClosure with hK
  have hKclosed : IsClosed (K : Set (H × H)) := G.isClosed_topologicalClosure
  haveI : CompleteSpace K := hKclosed.completeSpace_coe
  have hsymK : K ≤ adjointGraph K := by
    rw [hK, adjointGraph_topologicalClosure G]
    exact topologicalClosure_le_adjointGraph hsym
  set Ψ : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + c • (ContinuousLinearMap.fst ℂ H H) with hΨ
  set f : K →L[ℂ] H := Ψ.comp K.subtypeL with hf
  have hnorm : ∀ p : K, ‖(p : H × H)‖ ≤ ‖f p‖ := by
    intro p
    have hp : (inner ℂ (p : H × H).2 (p : H × H).1 : ℂ) = inner ℂ (p : H × H).1 (p : H × H).2 :=
      inner_self_swap hsymK p.2
    have h1 : ‖f p‖ ^ 2 = ‖(p : H × H).2‖ ^ 2 + ‖(p : H × H).1‖ ^ 2 := by
      simpa [hf, hΨ] using norm_shift_sq hp hc hc'
    have h2 : ‖(p : H × H)‖ ^ 2 ≤ ‖f p‖ ^ 2 := by
      rw [h1, Prod.norm_def]
      rcases max_cases ‖(p : H × H).1‖ ‖(p : H × H).2‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        nlinarith [norm_nonneg (p : H × H).1, norm_nonneg (p : H × H).2]
    exact le_of_sq_le_sq' (by nlinarith) (norm_nonneg _)
  have hanti : AntilipschitzWith 1 f := by
    refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
    have h := hnorm (p - q)
    simpa [dist_eq_norm, ← Submodule.coe_sub, map_sub] using h
  have hclosedrange : IsClosed (Set.range f) := hanti.isClosed_range f.uniformContinuous
  have hsubset : (shiftRange G c : Set H) ⊆ Set.range f := by
    intro v hv
    rw [SetLike.mem_coe, mem_shiftRange] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨⟨p, G.le_topologicalClosure hp⟩, rfl⟩
  have hrange : Set.range f = Set.univ := by
    have hd : Dense (Set.range f) := hdense.mono hsubset
    rw [← hclosedrange.closure_eq, hd.closure_eq]
  obtain ⟨p, hp⟩ : y ∈ Set.range f := by rw [hrange]; trivial
  exact ⟨(p : H × H), p.2, by simpa [hf, hΨ] using hp⟩

/-- **Basic criterion for essential self-adjointness** (von Neumann).  A densely defined
symmetric operator whose deficiency indices vanish, i.e. such that the ranges of `T + i` and
`T - i` are dense, is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_dense_shiftRange {G : Submodule ℂ (H × H)}
    (hd : Dense (domain G : Set H)) (hsym : G ≤ adjointGraph G)
    (h₁ : Dense (shiftRange G Complex.I : Set H))
    (h₂ : Dense (shiftRange G (-Complex.I) : Set H)) :
    IsEssentiallySelfAdjoint G := by
  refine ⟨hd, hsym, le_antisymm (topologicalClosure_le_adjointGraph hsym) ?_⟩
  rintro ⟨y, z⟩ hyz
  obtain ⟨p, hp, hpy⟩ :=
    shiftRange_closure_eq_top hsym (c := Complex.I) (by simp) (by simp) h₁ (z + Complex.I • y)
  have hpadj : p ∈ adjointGraph G := topologicalClosure_le_adjointGraph hsym hp
  have hdiff : ((y, z) - p) ∈ adjointGraph G := Submodule.sub_mem _ hyz hpadj
  have hkey : ((y, z) - p).2 = -(starRingEnd ℂ (-Complex.I)) • ((y, z) - p).1 := by
    have h : z - p.2 = -Complex.I • (y - p.1) := by
      rw [smul_sub]
      linear_combination (norm := module) -hpy
    simpa using h
  have hzero : ((y, z) - p).1 = 0 := by
    refine eq_zero_of_dense_shiftRange h₂ ?_
    rw [← hkey]
    exact hdiff
  have h2 : ((y, z) - p).2 = 0 := by rw [hkey, hzero]; simp
  have hEq : ((y, z) : H × H) = p := by
    have h3 := Prod.ext hzero h2
    simpa [sub_eq_zero] using h3
  rw [hEq]; exact hp

end Complete

end Brockian.Weyl

