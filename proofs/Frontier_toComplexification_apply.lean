/-
/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The required header is reproduced verbatim above; Lean 4 does not allow a module
-- docstring to precede `import`, so it is wrapped in a comment and repeated below.)

import Mathlib

/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Complex conjugation on a complexification -/

/-- Complex conjugation, viewed as a `ℚ`-linear endomorphism of `ℂ`. -/
noncomputable def conjQ : ℂ →ₗ[ℚ] ℂ :=
  (Complex.conjAe.toLinearMap).restrictScalars ℚ

/-- The conjugation `z ⊗ v ↦ conj z ⊗ v` on the complexification `ℂ ⊗[ℚ] V`
of a rational vector space `V`.  It is `ℚ`-linear (and conjugate-linear over `ℂ`). -/
noncomputable def conjTensor (V : Type) [AddCommGroup V] [Module ℚ V] :
    ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  LinearMap.rTensor V conjQ

/-! ## Pure rational Hodge structures -/

/-- A pure rational Hodge structure of weight `w`: a finite-dimensional `ℚ`-vector space `V`
together with a decomposition of its complexification `ℂ ⊗[ℚ] V` as an internal direct sum of
`ℂ`-subspaces `Hpq p q` indexed by the pairs `(p, q)` of natural numbers with `p + q = w`,
subject to Hodge symmetry: complex conjugation carries `Hpq p q` into `Hpq q p`.

This is the linear-algebra shadow of the singular cohomology `H^w(X, ℚ)` of a smooth complex
projective variety `X`. -/
structure HodgeStructure (w : ℕ) where
  /-- The underlying rational vector space. -/
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module ℚ V]
  [finiteDimensional : FiniteDimensional ℚ V]
  /-- The `(p, q)`-piece of the Hodge decomposition of the complexification. -/
  Hpq : ℕ → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The pieces of weight `w` decompose the complexification. -/
  isInternal :
    DirectSum.IsInternal fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = w} => Hpq pq.1.1 pq.1.2
  /-- Hodge symmetry. -/
  conj_symm : ∀ p q, ∀ x ∈ Hpq p q, conjTensor V x ∈ Hpq q p

attribute [instance] HodgeStructure.addCommGroup HodgeStructure.module
  HodgeStructure.finiteDimensional

/-- The canonical `ℚ`-linear inclusion `v ↦ 1 ⊗ v` of `V` into its complexification. -/
noncomputable def toComplexification (V : Type) [AddCommGroup V] [Module ℚ V] :
    V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.mk ℚ ℂ V 1

@[simp]
theorem toComplexification_apply (V : Type) [AddCommGroup V] [Module ℚ V] (v : V) :
    toComplexification V v = (1 : ℂ) ⊗ₜ[ℚ] v := rfl

/-- The space of **Hodge classes** of a weight-`2k` rational Hodge structure: the rational
vectors whose image in the complexification lies in the `(k, k)`-piece. -/
noncomputable def hodgeClasses {k : ℕ} (H : HodgeStructure (2 * k)) : Submodule ℚ H.V :=
  Submodule.comap (toComplexification H.V) ((H.Hpq k k).restrictScalars ℚ)

theorem mem_hodgeClasses_iff {k : ℕ} (H : HodgeStructure (2 * k)) (v : H.V) :
    v ∈ hodgeClasses H ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.Hpq k k := Iff.rfl

/-! ## The Hodge conjecture -/

/-- The cohomological data attached to a smooth complex projective variety in codimension `k`:
the weight-`2k` Hodge structure `H^{2k}(X, ℚ)` together with the subspace `alg` spanned by the
classes of algebraic cycles of codimension `k`.  Cycle classes are always Hodge classes, which is
recorded by `alg_le`. -/
structure HodgeDatum (k : ℕ) where
  /-- The weight-`2k` Hodge structure. -/
  hs : HodgeStructure (2 * k)
  /-- The subspace spanned by the classes of algebraic cycles of codimension `k`. -/
  alg : Submodule ℚ hs.V
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le : alg ≤ hodgeClasses hs

/-- **The Hodge conjecture** for a given datum: every Hodge class is a rational linear
combination of classes of algebraic cycles. -/
def HodgeConjecture {k : ℕ} (D : HodgeDatum k) : Prop :=
  hodgeClasses D.hs ≤ D.alg

/-- Reformulation: the Hodge conjecture holds for `D` exactly when the Hodge classes coincide
with the algebraic classes. -/
theorem hodgeConjecture_iff_eq {k : ℕ} (D : HodgeDatum k) :
    HodgeConjecture D ↔ hodgeClasses D.hs = D.alg :=
  ⟨fun h => le_antisymm h D.alg_le, fun h => h.le⟩

/-! ## Elementary criteria -/

/-- If every algebraic class is already everything, the conjecture holds. -/
theorem hodgeConjecture_of_alg_eq_top {k : ℕ} (D : HodgeDatum k) (h : D.alg = ⊤) :
    HodgeConjecture D := by
  simp [HodgeConjecture, h]

/-- If there are no nonzero Hodge classes, the conjecture holds. -/
theorem hodgeConjecture_of_hodgeClasses_eq_bot {k : ℕ} (D : HodgeDatum k)
    (h : hodgeClasses D.hs = ⊥) : HodgeConjecture D := by
  simp [HodgeConjecture, h]

/-- It suffices to exhibit an algebraic spanning set of the Hodge classes: a Lean-checked
reduction of the conjecture to a generation statement. -/
theorem hodgeConjecture_of_span {k : ℕ} (D : HodgeDatum k) (S : Set D.hs.V)
    (hspan : hodgeClasses D.hs = Submodule.span ℚ S) (hS : S ⊆ (D.alg : Set D.hs.V)) :
    HodgeConjecture D := by
  rw [HodgeConjecture, hspan, Submodule.span_le]
  exact hS

/-! ## Transfer along isomorphisms of Hodge data -/

/-- A `ℚ`-linear isomorphism of the underlying spaces which respects the Hodge decompositions
transports Hodge classes. -/
theorem hodgeClasses_map_of_isom {k : ℕ} (H K : HodgeStructure (2 * k)) (f : H.V ≃ₗ[ℚ] K.V)
    (hf : ∀ p q, (H.Hpq p q).map (LinearMap.baseChange ℂ (f : H.V →ₗ[ℚ] K.V)) = K.Hpq p q)
    (w : K.V) (hw : w ∈ hodgeClasses K) : f.symm w ∈ hodgeClasses H := by
  have hcomp : (LinearMap.baseChange ℂ (f.symm : K.V →ₗ[ℚ] H.V)) ∘ₗ
      (LinearMap.baseChange ℂ (f : H.V →ₗ[ℚ] K.V)) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp]
    have : ((f.symm : K.V →ₗ[ℚ] H.V) ∘ₗ (f : H.V →ₗ[ℚ] K.V)) = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.baseChange_id]
  have hback : (K.Hpq k k).map (LinearMap.baseChange ℂ (f.symm : K.V →ₗ[ℚ] H.V)) = H.Hpq k k := by
    rw [← hf k k, ← Submodule.map_comp, hcomp, Submodule.map_id]
  rw [mem_hodgeClasses_iff] at hw ⊢
  rw [← hback]
  refine ⟨(1 : ℂ) ⊗ₜ[ℚ] w, hw, ?_⟩
  simp

/-- **Functoriality / reduction step.**  If two Hodge data are isomorphic (via a `ℚ`-linear
isomorphism respecting the Hodge decompositions and matching the algebraic classes), then the
Hodge conjecture for one implies it for the other. -/
theorem hodgeConjecture_transfer {k : ℕ} (D E : HodgeDatum k) (f : D.hs.V ≃ₗ[ℚ] E.hs.V)
    (hf : ∀ p q, (D.hs.Hpq p q).map (LinearMap.baseChange ℂ (f : D.hs.V →ₗ[ℚ] E.hs.V))
      = E.hs.Hpq p q)
    (hfa : D.alg.map (f : D.hs.V →ₗ[ℚ] E.hs.V) = E.alg) (hD : HodgeConjecture D) :
    HodgeConjecture E := by
  intro w hw
  have hv : f.symm w ∈ hodgeClasses D.hs := hodgeClasses_map_of_isom D.hs E.hs f hf w hw
  have : f.symm w ∈ D.alg := hD hv
  have himg : f (f.symm w) ∈ D.alg.map (f : D.hs.V →ₗ[ℚ] E.hs.V) := ⟨_, this, rfl⟩
  rw [hfa] at himg
  simpa using himg

/-! ## The base case: degree zero -/

/-- **Base case of the Hodge conjecture.**  If `H^{2k}(X, ℚ)` is one-dimensional and contains
some nonzero algebraic class, then every Hodge class of degree `2k` is algebraic. -/
theorem hodgeConjecture_of_finrank_one {k : ℕ} (D : HodgeDatum k)
    (hrank : Module.finrank ℚ D.hs.V = 1) (hne : D.alg ≠ ⊥) : HodgeConjecture D := by
  refine hodgeConjecture_of_alg_eq_top D ?_
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : Submodule.span ℚ ({x} : Set D.hs.V) = ⊤ := by
    have h1 : Module.finrank ℚ (Submodule.span ℚ ({x} : Set D.hs.V)) = 1 :=
      finrank_span_singleton hx0
    exact Submodule.eq_top_of_finrank_eq (by rw [h1, hrank])
  refine top_le_iff.mp ?_
  rw [← hspan, Submodule.span_le, Set.singleton_subset_iff]
  exact hxmem

/-- **Base case of the Hodge conjecture in degree `0`.**  For a connected variety `H^0(X, ℚ)` is
one-dimensional and contains the (algebraic) fundamental class of `X`; hence all Hodge classes of
degree `0` are algebraic. -/
theorem hodgeConjecture_degree_zero (D : HodgeDatum 0) (hrank : Module.finrank ℚ D.hs.V = 1)
    (hne : D.alg ≠ ⊥) : HodgeConjecture D :=
  hodgeConjecture_of_finrank_one D hrank hne

/-! ## A concrete example: the framework is non-vacuous

We build, for every `k`, the Hodge datum of a variety whose `2k`-th cohomology is one-dimensional
and purely of type `(k, k)`, spanned by an algebraic class — for `k = 0` this is `H^0` of a
connected variety, and for `k = 1` it is `H^2(ℙ^1, ℚ)` with its class of a point. -/

/-- The Hodge decomposition of a one-dimensional weight-`2k` structure concentrated in
bidegree `(k, k)`. -/
noncomputable def unitHpq (k : ℕ) : ℕ → ℕ → Submodule ℂ (ℂ ⊗[ℚ] ℚ) :=
  fun p q => if p = k ∧ q = k then ⊤ else ⊥

theorem unitHpq_isInternal (k : ℕ) :
    DirectSum.IsInternal
      fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = 2 * k} => unitHpq k pq.1.1 pq.1.2 := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    by_cases h : i.1.1 = k ∧ i.1.2 = k
    · have hbot : (⨆ (j : {pq : ℕ × ℕ // pq.1 + pq.2 = 2 * k}) (_ : j ≠ i),
          unitHpq k j.1.1 j.1.2) = ⊥ := by
        refine iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => ?_
        have hne : ¬ (j.1.1 = k ∧ j.1.2 = k) := by
          rintro ⟨h1, h2⟩
          exact hj (Subtype.ext (Prod.ext (h1.trans h.1.symm) (h2.trans h.2.symm)))
        simp [unitHpq, hne]
      simp [hbot]
    · simp [unitHpq, h]
  · refine le_antisymm le_top ?_
    have h : unitHpq k k k
        ≤ ⨆ i : {pq : ℕ × ℕ // pq.1 + pq.2 = 2 * k}, unitHpq k i.1.1 i.1.2 :=
      le_iSup (fun i : {pq : ℕ × ℕ // pq.1 + pq.2 = 2 * k} => unitHpq k i.1.1 i.1.2)
        ⟨(k, k), by ring⟩
    simpa [unitHpq] using h

/-- The one-dimensional weight-`2k` Hodge structure of type `(k, k)`. -/
noncomputable def unitHodgeStructure (k : ℕ) : HodgeStructure (2 * k) where
  V := ℚ
  Hpq := unitHpq k
  isInternal := unitHpq_isInternal k
  conj_symm := by
    intro p q x hx
    by_cases h : p = k ∧ q = k
    · simp [unitHpq, h]
    · have hx0 : x = 0 := by
        rw [unitHpq, if_neg h] at hx
        simpa using hx
      simp [hx0]

/-- In the one-dimensional structure of type `(k, k)`, every rational class is a Hodge class. -/
theorem hodgeClasses_unitHodgeStructure (k : ℕ) : hodgeClasses (unitHodgeStructure k) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  rw [mem_hodgeClasses_iff]
  simp [unitHodgeStructure, unitHpq]

/-- The Hodge datum of a variety with one-dimensional `H^{2k}` of type `(k,k)` spanned by an
algebraic class (e.g. `H^0` of a connected variety, or `H^2(ℙ^1, ℚ)`). -/
noncomputable def unitHodgeDatum (k : ℕ) : HodgeDatum k where
  hs := unitHodgeStructure k
  alg := ⊤
  alg_le := (hodgeClasses_unitHodgeStructure k).ge

/-- The Hodge conjecture holds for the datum `unitHodgeDatum k`; in particular the notions above
are not vacuous. -/
theorem hodgeConjecture_unitHodgeDatum (k : ℕ) : HodgeConjecture (unitHodgeDatum k) :=
  hodgeConjecture_of_finrank_one _ (by simp [unitHodgeDatum, unitHodgeStructure])
    (Submodule.ne_bot_iff _ |>.mpr ⟨(1 : ℚ), Submodule.mem_top, by norm_num⟩)

/-- The abstract framework does not, by itself, imply the conjecture: for a datum in which the
subspace of algebraic classes is taken to be zero while Hodge classes exist, the conclusion fails.
The geometric input (that `alg` really is spanned by cycle classes of a smooth projective variety)
is therefore essential. -/
theorem exists_hodgeDatum_not_hodgeConjecture (k : ℕ) :
    ∃ D : HodgeDatum k, ¬ HodgeConjecture D := by
  refine ⟨⟨unitHodgeStructure k, ⊥, bot_le⟩, ?_⟩
  intro h
  have h1 : (1 : ℚ) ∈ (⊥ : Submodule ℚ (unitHodgeStructure k).V) := by
    refine h ?_
    show (1 : ℚ) ∈ hodgeClasses (unitHodgeStructure k)
    rw [hodgeClasses_unitHodgeStructure]
    exact Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  norm_num at h1

/-! ## Main statement -/

/-- **Hodge statement.**

The Hodge conjecture, `Frontier.HodgeConjecture`, asserts that for the cohomological datum of a
smooth complex projective variety in codimension `k` — a pure rational Hodge structure of weight
`2k` together with the subspace of algebraic cycle classes — every Hodge class (a rational class
lying in the `(k,k)`-piece of the Hodge decomposition) is a rational combination of classes of
algebraic cycles.

This theorem records what is proved here:

1. (Base case) the conjecture holds whenever `H^{2k}` is one-dimensional and carries a nonzero
   algebraic class; in particular it holds in degree `0`, where `H^0(X, ℚ)` of a connected `X` is
   one-dimensional and spanned by the (algebraic) fundamental class;
2. (Reduction) the conjecture is invariant under isomorphism of Hodge data, so it only depends on
   the isomorphism class of the pair (Hodge structure, algebraic classes);
3. (Reduction) it suffices to produce an algebraic spanning set of the space of Hodge classes;
4. the degenerate cases (no nonzero Hodge classes, or everything algebraic) hold;
5. the framework is non-vacuous: `unitHodgeDatum k` is a genuine Hodge datum for every `k`
   (the model for `H^0` of a connected variety, and for `H^2(ℙ^1, ℚ)` when `k = 1`), and the
   conjecture holds for it. -/
theorem hodge_statement :
    (∀ (k : ℕ) (D : HodgeDatum k), Module.finrank ℚ D.hs.V = 1 → D.alg ≠ ⊥ →
      HodgeConjecture D) ∧
    (∀ D : HodgeDatum 0, Module.finrank ℚ D.hs.V = 1 → D.alg ≠ ⊥ → HodgeConjecture D) ∧
    (∀ (k : ℕ) (D E : HodgeDatum k) (f : D.hs.V ≃ₗ[ℚ] E.hs.V),
      (∀ p q, (D.hs.Hpq p q).map (LinearMap.baseChange ℂ (f : D.hs.V →ₗ[ℚ] E.hs.V))
        = E.hs.Hpq p q) →
      D.alg.map (f : D.hs.V →ₗ[ℚ] E.hs.V) = E.alg → HodgeConjecture D → HodgeConjecture E) ∧
    (∀ (k : ℕ) (D : HodgeDatum k) (S : Set D.hs.V),
      hodgeClasses D.hs = Submodule.span ℚ S → S ⊆ (D.alg : Set D.hs.V) → HodgeConjecture D) ∧
    (∀ (k : ℕ) (D : HodgeDatum k), hodgeClasses D.hs = ⊥ → HodgeConjecture D) ∧
    (∀ (k : ℕ) (D : HodgeDatum k), D.alg = ⊤ → HodgeConjecture D) ∧
    (∀ k : ℕ, HodgeConjecture (unitHodgeDatum k)) :=
  ⟨fun _ D hrank hne => hodgeConjecture_of_finrank_one D hrank hne,
   hodgeConjecture_degree_zero,
   fun _ D E f hf hfa hD => hodgeConjecture_transfer D E f hf hfa hD,
   fun _ D S hspan hS => hodgeConjecture_of_span D S hspan hS,
   fun _ D h => hodgeConjecture_of_hodgeClasses_eq_bot D h,
   fun _ D h => hodgeConjecture_of_alg_eq_top D h,
   hodgeConjecture_unitHodgeDatum⟩

end Frontier

