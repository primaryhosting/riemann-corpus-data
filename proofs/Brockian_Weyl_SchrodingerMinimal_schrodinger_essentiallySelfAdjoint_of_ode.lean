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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped LinearPMap ComplexConjugate
open MeasureTheory

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Part 1: the abstract deficiency criterion

We prove the *basic criterion of essential self-adjointness*: a densely defined symmetric
operator `T` on a complex Hilbert space is essentially self-adjoint as soon as the two
deficiency spaces `ker (T† ∓ i)` are trivial.

Essential self-adjointness is expressed as `IsSelfAdjoint T†` (equivalently `T†† = T†`,
i.e. the closure `T†† = T̄` of `T` is self-adjoint).
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The adjoint operation is antitone. -/
theorem adjoint_le_adjoint_of_le {S R : H →ₗ.[ℂ] H} (hS : Dense (S.domain : Set H)) (h : S ≤ R) :
    R† ≤ S† := by
  have hR : Dense (R.domain : Set H) := hS.mono (fun x hx => h.1 hx)
  refine LinearPMap.le_of_le_graph ?_
  rintro ⟨y, w⟩ hyw
  obtain ⟨⟨y', hy'⟩, hEq⟩ := (LinearPMap.mem_graph_iff _).mp hyw
  obtain ⟨rfl, rfl⟩ := hEq
  have key : ∀ x : S.domain, ⟪R† ⟨y', hy'⟩, (x : H)⟫ = ⟪y', S x⟫ := by
    intro x
    have h1 := (LinearPMap.adjoint_isFormalAdjoint hR) ⟨y', hy'⟩ ⟨(x : H), h.1 x.2⟩
    rw [h1, h.2 (x := x) (y := ⟨(x : H), h.1 x.2⟩) rfl]
  have hmem : y' ∈ S†.domain := LinearPMap.mem_adjoint_domain_of_exists y' ⟨_, key⟩
  have hval : S† ⟨y', hmem⟩ = R† ⟨y', hy'⟩ := LinearPMap.adjoint_apply_eq hS ⟨y', hmem⟩ key
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨y', hmem⟩, by simp [hval]⟩

omit [CompleteSpace H] in
theorem mem_closure_of_mem_topologicalClosure {s : Submodule ℂ (H × H)} {a : H × H}
    (h : a ∈ s.topologicalClosure) : a ∈ closure (s : Set (H × H)) := by
  rw [← Submodule.topologicalClosure_coe]; exact h

variable (T : H →ₗ.[ℂ] H)

/-- The closure of the graph of `T` is contained in the graph of the adjoint, for symmetric `T`. -/
theorem graphClosure_le_adjoint_graph (hd : Dense (T.domain : Set H)) (hsym : T.IsFormalAdjoint T) :
    T.graph.topologicalClosure ≤ T†.graph :=
  Submodule.topologicalClosure_minimal _
    (LinearPMap.le_graph_of_le (hsym.le_adjoint hd)) (LinearPMap.adjoint_isClosed hd)

omit [CompleteSpace H] in
/-- Symmetry passes to the closure of the graph. -/
theorem inner_graphClosure_symm (hsym : T.IsFormalAdjoint T) {p q : H × H}
    (hp : p ∈ T.graph.topologicalClosure) (hq : q ∈ T.graph.topologicalClosure) :
    ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫ := by
  have base : ∀ a b : H × H, a ∈ T.graph → b ∈ T.graph → ⟪a.2, b.1⟫ = ⟪a.1, b.2⟫ := by
    rintro a b ha hb
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).mp ha
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).mp hb
    rw [← hx1, ← hx2, ← hy1, ← hy2]
    exact hsym x y
  have step1 : ∀ b ∈ T.graph, ∀ a ∈ T.graph.topologicalClosure, ⟪a.2, b.1⟫ = ⟪a.1, b.2⟫ := by
    intro b hb a ha
    have hc : IsClosed {a : H × H | ⟪a.2, b.1⟫ = ⟪a.1, b.2⟫} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact closure_minimal (fun a ha => base a b ha hb) hc (mem_closure_of_mem_topologicalClosure ha)
  have hc2 : IsClosed {b : H × H | ⟪p.2, b.1⟫ = ⟪p.1, b.2⟫} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact closure_minimal (fun b hb => step1 b hb p hp) hc2 (mem_closure_of_mem_topologicalClosure hq)

omit [CompleteSpace H] in
/-- For a point of the closure of the graph of a symmetric operator,
`‖y + c • x‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2` when `c = ± i`. -/
theorem norm_sq_add_smul_of_mem_graphClosure (hsym : T.IsFormalAdjoint T) {c : ℂ}
    (hc : c = Complex.I ∨ c = -Complex.I) {p : H × H} (hp : p ∈ T.graph.topologicalClosure) :
    ‖p.2 + c • p.1‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  have hreal : ⟪p.2, p.1⟫ = ⟪p.1, p.2⟫ := inner_graphClosure_symm T hsym hp hp
  have him : (⟪p.2, p.1⟫ : ℂ).im = 0 := by
    have h := inner_conj_symm (𝕜 := ℂ) p.1 p.2
    rw [← hreal] at h
    exact Complex.conj_eq_iff_im.mp h
  have hnc : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, hnc]
  have hzero : (RCLike.re (c * ⟪p.2, p.1⟫) : ℝ) = 0 := by
    rcases hc with rfl | rfl <;> simp [Complex.mul_re, him]
  rw [hzero]
  ring

/-- The continuous linear map `(x, y) ↦ y + c • x`. -/
noncomputable def combCLM (c : ℂ) : (H × H) →L[ℂ] H :=
  (ContinuousLinearMap.snd ℂ H H) + c • (ContinuousLinearMap.fst ℂ H H)

omit [CompleteSpace H] in
@[simp] theorem combCLM_apply (c : ℂ) (p : H × H) : combCLM c p = p.2 + c • p.1 := rfl

/-- The image of the closed graph under `(x, y) ↦ y + c • x` is a closed submodule. -/
theorem isClosed_map_combCLM (hsym : T.IsFormalAdjoint T) {c : ℂ}
    (hc : c = Complex.I ∨ c = -Complex.I) :
    IsClosed (((Submodule.map (combCLM c).toLinearMap T.graph.topologicalClosure :
      Submodule ℂ H)) : Set H) := by
  set K := T.graph.topologicalClosure with hK
  haveI hKc : IsClosed (K : Set (H × H)) := Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace K := IsClosed.completeSpace_coe
  set f : K →L[ℂ] H := (combCLM c).comp K.subtypeL with hf
  have hanti : AntilipschitzWith 1 f := by
    apply AddMonoidHomClass.antilipschitz_of_bound
    intro p
    have h2 : ‖f p‖ ^ 2 = ‖(p : H × H).1‖ ^ 2 + ‖(p : H × H).2‖ ^ 2 := by
      simpa [hf] using norm_sq_add_smul_of_mem_graphClosure T hsym hc p.2
    have h3 : ‖(p : H × H)‖ = max ‖(p : H × H).1‖ ‖(p : H × H).2‖ := Prod.norm_def _
    have hp1 : (0:ℝ) ≤ ‖(p : H × H).1‖ := norm_nonneg _
    have hp2 : (0:ℝ) ≤ ‖(p : H × H).2‖ := norm_nonneg _
    have hsq : ‖p‖ ^ 2 ≤ ‖f p‖ ^ 2 := by
      rw [h2]
      have hpp : ‖p‖ = ‖(p : H × H)‖ := rfl
      rw [hpp, h3]
      rcases max_cases ‖(p : H × H).1‖ ‖(p : H × H).2‖ with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rw [he] <;> nlinarith
    have hpn : (0:ℝ) ≤ ‖p‖ := norm_nonneg _
    have hfn : (0:ℝ) ≤ ‖f p‖ := norm_nonneg _
    simp only [NNReal.coe_one, one_mul]
    nlinarith
  have hrange : IsClosed (Set.range f) := hanti.isClosed_range f.uniformContinuous
  convert hrange using 1
  rw [Submodule.map_coe]
  ext z
  simp [hf, Set.mem_image, Set.mem_range]

/-- If the deficiency space for `c` is trivial then the image of the graph of `T` under
`(x,y) ↦ y + c • x` is dense (its orthogonal complement is trivial). -/
theorem orthogonal_map_combCLM_graph_eq_bot (hd : Dense (T.domain : Set H)) {c : ℂ}
    (hc : c = Complex.I ∨ c = -Complex.I)
    (hker : ∀ u : T†.domain, T† u = c • (u : H) → (u : H) = 0) :
    (Submodule.map (combCLM c).toLinearMap T.graph : Submodule ℂ H)ᗮ = ⊥ := by
  have hconj : (starRingEnd ℂ) c = -c := by rcases hc with rfl | rfl <;> simp
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal] at hw
  have key : ∀ x : T.domain, ⟪c • w, (x : H)⟫ = ⟪w, T x⟫ := by
    intro x
    have hmem : (T x + c • (x : H)) ∈ (Submodule.map (combCLM c).toLinearMap T.graph) := by
      refine ⟨((x : H), T x), T.mem_graph x, ?_⟩
      simp [combCLM]
    have h0 := hw _ hmem
    rw [inner_add_left, inner_smul_left] at h0
    have h1 : ⟪T x, w⟫ = -((starRingEnd ℂ) c * ⟪(x : H), w⟫) := by linear_combination h0
    have h2 : ⟪w, T x⟫ = -(c * ⟪w, (x : H)⟫) := by
      rw [← inner_conj_symm (𝕜 := ℂ), h1]
      simp [inner_conj_symm]
    rw [inner_smul_left, h2, hconj]
    ring
  have hmem : w ∈ T†.domain := LinearPMap.mem_adjoint_domain_of_exists w ⟨_, key⟩
  exact hker ⟨w, hmem⟩ (LinearPMap.adjoint_apply_eq hd ⟨w, hmem⟩ key)

/-- Under the deficiency hypotheses, `(x, y) ↦ y + c • x` maps the closure of the graph
of `T` onto the whole space. -/
theorem map_combCLM_graphClosure_eq_top (hd : Dense (T.domain : Set H))
    (hsym : T.IsFormalAdjoint T) {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I)
    (hker : ∀ u : T†.domain, T† u = c • (u : H) → (u : H) = 0) :
    (Submodule.map (combCLM c).toLinearMap T.graph.topologicalClosure : Submodule ℂ H) = ⊤ := by
  set K : Submodule ℂ H := Submodule.map (combCLM c).toLinearMap T.graph.topologicalClosure with hKdef
  haveI hKc : IsClosed (K : Set H) := isClosed_map_combCLM T hsym hc
  haveI : CompleteSpace K := IsClosed.completeSpace_coe
  have hle : (Submodule.map (combCLM c).toLinearMap T.graph : Submodule ℂ H) ≤ K :=
    Submodule.map_mono (Submodule.le_topologicalClosure _)
  have h1 : Kᗮ = ⊥ :=
    le_bot_iff.mp ((orthogonal_map_combCLM_graph_eq_bot T hd hc hker) ▸
      Submodule.orthogonal_le hle)
  exact Submodule.orthogonal_eq_bot_iff.mp h1

/-- Under the deficiency hypotheses, the graph of the adjoint is contained in the closure of
the graph of `T`. -/
theorem adjoint_graph_le_graphClosure (hd : Dense (T.domain : Set H))
    (hsym : T.IsFormalAdjoint T)
    (hdef : ∀ c : ℂ, (c = Complex.I ∨ c = -Complex.I) →
      ∀ u : T†.domain, T† u = c • (u : H) → (u : H) = 0) :
    T†.graph ≤ T.graph.topologicalClosure := by
  have hsurj := map_combCLM_graphClosure_eq_top T hd hsym (Or.inl rfl) (hdef Complex.I (Or.inl rfl))
  rintro ⟨u, w⟩ huw
  obtain ⟨⟨u', hu'⟩, hEq⟩ := (LinearPMap.mem_graph_iff _).mp huw
  obtain ⟨rfl, rfl⟩ := hEq
  -- surjectivity gives a point of the closed graph with the same value under `y ↦ y + i • x`
  have hmem : (T† ⟨u', hu'⟩ + Complex.I • u') ∈
      (Submodule.map (combCLM Complex.I).toLinearMap T.graph.topologicalClosure) := by
    rw [hsurj]; trivial
  obtain ⟨⟨p1, p2⟩, hp, hpv⟩ := hmem
  obtain ⟨⟨x, hx⟩, hx1, hx2⟩ :=
    (LinearPMap.mem_graph_iff _).mp (graphClosure_le_adjoint_graph T hd hsym hp)
  simp only at hx1 hx2
  subst hx1
  subst hx2
  have hpv' : T† ⟨x, hx⟩ + Complex.I • x = T† ⟨u', hu'⟩ + Complex.I • u' := hpv
  -- `u' - x` lies in the deficiency space for `-i`
  have hdiff : T† (⟨u', hu'⟩ - ⟨x, hx⟩) =
      (-Complex.I) • ((⟨u', hu'⟩ - ⟨x, hx⟩ : T†.domain) : H) := by
    have hkey : T† ⟨u', hu'⟩ - T† ⟨x, hx⟩ = (-Complex.I) • (u' - x) := by
      rw [smul_sub, neg_smul]
      linear_combination (norm := module) -hpv'
    rw [LinearPMap.map_sub]
    simpa using hkey
  have hzero := hdef (-Complex.I) (Or.inr rfl) (⟨u', hu'⟩ - ⟨x, hx⟩) hdiff
  have hux : u' = x := by
    have h0 : u' - x = 0 := by simpa using hzero
    exact sub_eq_zero.mp h0
  subst hux
  exact hp

/-- **Basic criterion of essential self-adjointness.** A densely defined symmetric operator
whose two deficiency spaces are trivial is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_deficiency_trivial (hd : Dense (T.domain : Set H))
    (hsym : T.IsFormalAdjoint T)
    (hdef : ∀ c : ℂ, (c = Complex.I ∨ c = -Complex.I) →
      ∀ u : T†.domain, T† u = c • (u : H) → (u : H) = 0) :
    IsSelfAdjoint (T†) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hTle : T ≤ T† := hsym.le_adjoint hd
  have hdadj : Dense (T†.domain : Set H) := hd.mono (fun x hx => hTle.1 hx)
  have h1 : T†† ≤ T† := adjoint_le_adjoint_of_le hd hTle
  have h2 : T†.graph ≤ T.graph.topologicalClosure := adjoint_graph_le_graphClosure T hd hsym hdef
  have hsym2 : T†.IsFormalAdjoint T† := by
    intro u v
    exact inner_graphClosure_symm T hsym (h2 (T†.mem_graph u)) (h2 (T†.mem_graph v))
  have h3 : T† ≤ T†† := hsym2.le_adjoint hdadj
  exact le_antisymm h1 h3

end Abstract

end Brockian.Weyl.SchrodingerMinimal

