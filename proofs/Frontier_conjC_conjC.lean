/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The setting

Mathlib does not (yet) contain the theory of smooth projective complex varieties,
singular cohomology with its Hodge decomposition, or the cycle class map.  We therefore
formalize the Hodge conjecture in the standard *linear-algebra* form it takes once the
geometric input is available:

* `V` plays the role of the singular cohomology group `H^{2p}(X, ℚ)` of a smooth
  projective complex variety `X`;
* `ℂ ⊗[ℚ] V` is its complexification `H^{2p}(X, ℂ)`;
* a `HodgeStructure V w` is a Hodge decomposition of weight `w` on `V`, i.e. a
  bigrading `H^{a,b}` of `ℂ ⊗[ℚ] V` concentrated in bidegrees with `a + b = w`
  and exchanged by complex conjugation;
* `hodgeClasses H p` is the ℚ-subspace of *Hodge classes*: rational classes whose
  image in the complexification lies in the `(p,p)` piece;
* an `AlgebraicClasses H p` is a subspace `A` of classes of algebraic cycles; the
  geometric fact that algebraic cycle classes are Hodge classes is recorded as the
  field `alg_le_hodge`.

The Hodge conjecture then reads: `hodgeClasses H p ≤ A`, i.e. every Hodge class is a
rational combination of classes of algebraic cycles.
-/

section Conjugation

variable (V : Type) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V`, as a `ℚ`-linear map. -/
noncomputable def conjC : (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  LinearMap.rTensor V ((Complex.conjAe.toLinearMap).restrictScalars ℚ)

@[simp] theorem conjC_tmul (z : ℂ) (v : V) :
    conjC V (z ⊗ₜ[ℚ] v) = (starRingEnd ℂ) z ⊗ₜ[ℚ] v := rfl

theorem conjC_conjC (x : ℂ ⊗[ℚ] V) : conjC V (conjC V x) = x := by
  induction x with
  | zero => simp
  | tmul z v => simp
  | add x y hx hy => simp [map_add, hx, hy]

theorem conjC_surjective : Function.Surjective (conjC V) :=
  fun x => ⟨conjC V x, conjC_conjC V x⟩

end Conjugation

variable {V : Type} [AddCommGroup V] [Module ℚ V]

/-- A (pure) rational Hodge structure of weight `w` on the ℚ-vector space `V`:
a bigrading `F a b = H^{a,b}` of the complexification `ℂ ⊗[ℚ] V`, concentrated in
bidegrees of total degree `w`, whose pieces are independent and span, and which is
exchanged by complex conjugation. -/
structure HodgeStructure (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) where
  /-- The `(a,b)` piece `H^{a,b}` of the Hodge decomposition. -/
  F : ℤ → ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- The decomposition is concentrated in total degree `w`. -/
  weight : ∀ a b : ℤ, a + b ≠ w → F a b = ⊥
  /-- The pieces are independent. -/
  indep : iSupIndep fun ab : ℤ × ℤ => F ab.1 ab.2
  /-- The pieces span the complexification. -/
  spanning : (⨆ ab : ℤ × ℤ, F ab.1 ab.2) = ⊤
  /-- Complex conjugation exchanges `H^{a,b}` and `H^{b,a}`. -/
  conj_symm : ∀ a b : ℤ,
    ((F a b).restrictScalars ℚ).map (conjC V) = (F b a).restrictScalars ℚ

/-- The canonical map `V → ℂ ⊗[ℚ] V`, `v ↦ 1 ⊗ v`. -/
noncomputable def toCx : V →ₗ[ℚ] ℂ ⊗[ℚ] V := TensorProduct.mk ℚ ℂ V 1

/-- The space of **Hodge classes** of type `(p,p)`: rational classes whose image in the
complexification lies in `H^{p,p}`. -/
noncomputable def hodgeClasses {w : ℤ} (H : HodgeStructure V w) (p : ℤ) :
    Submodule ℚ V :=
  Submodule.comap toCx ((H.F p p).restrictScalars ℚ)

theorem toCx_injective : Function.Injective (toCx (V := V)) := by
  have hinj : Function.Injective (Algebra.linearMap ℚ ℂ) := fun a b hab => by
    simpa [Algebra.linearMap_apply] using hab
  have h1 : Function.Injective (⇑(LinearMap.rTensor V (Algebra.linearMap ℚ ℂ))) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := V) _ hinj
  have h2 : ∀ v : V, (LinearMap.rTensor V (Algebra.linearMap ℚ ℂ))
      ((TensorProduct.lid ℚ V).symm v) = toCx v := by
    intro v; simp [toCx, Algebra.linearMap_apply]
  intro a b hab
  have h3 : (LinearMap.rTensor V (Algebra.linearMap ℚ ℂ)) ((TensorProduct.lid ℚ V).symm a)
      = (LinearMap.rTensor V (Algebra.linearMap ℚ ℂ)) ((TensorProduct.lid ℚ V).symm b) := by
    rw [h2, h2, hab]
  exact (TensorProduct.lid ℚ V).symm.injective (h1 h3)

theorem mem_hodgeClasses {w : ℤ} (H : HodgeStructure V w) (p : ℤ) (v : V) :
    v ∈ hodgeClasses H p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.F p p := Iff.rfl

/-- A space of algebraic cycle classes inside `V`, subject to the geometric fact that
classes of algebraic cycles are Hodge classes. -/
structure AlgebraicClasses {w : ℤ} (H : HodgeStructure V w) (p : ℤ) where
  /-- The ℚ-span of the classes of algebraic cycles of codimension `p`. -/
  A : Submodule ℚ V
  /-- Algebraic cycle classes are Hodge classes. -/
  alg_le_hodge : A ≤ hodgeClasses H p

/-- **The Hodge conjecture** for the datum `(H, p, C)`: every Hodge class of type `(p,p)`
is a rational linear combination of classes of algebraic cycles. -/
def HodgeConjectureFor {w : ℤ} (H : HodgeStructure V w) (p : ℤ)
    (C : AlgebraicClasses H p) : Prop :=
  hodgeClasses H p ≤ C.A

/-!
## Reformulations
-/

/-- Contrapositive form: the conjecture holds exactly when there is no non-algebraic
Hodge class. -/
theorem hodgeConjectureFor_iff_not_exists {w : ℤ} (H : HodgeStructure V w) (p : ℤ)
    (C : AlgebraicClasses H p) :
    HodgeConjectureFor H p C ↔ ¬ ∃ v : V, v ∈ hodgeClasses H p ∧ v ∉ C.A := by
  constructor
  · rintro h ⟨v, hv, hv'⟩
    exact hv' (h hv)
  · intro h v hv
    by_contra hv'
    exact h ⟨v, hv, hv'⟩

/-- Since algebraic classes are always Hodge classes, the conjecture is equivalent to the
equality of the space of Hodge classes and the space of algebraic classes. -/
theorem hodgeConjectureFor_iff_eq {w : ℤ} (H : HodgeStructure V w) (p : ℤ)
    (C : AlgebraicClasses H p) :
    HodgeConjectureFor H p C ↔ hodgeClasses H p = C.A :=
  ⟨fun h => le_antisymm h C.alg_le_hodge, fun h => h.le⟩

/-- Reduction to a spanning family: the conjecture holds iff the space of Hodge classes
is spanned by algebraic classes.  (So it suffices to exhibit algebraic cycles whose
classes span the Hodge classes, e.g. a basis of them.) -/
theorem hodgeConjectureFor_iff_span {w : ℤ} (H : HodgeStructure V w) (p : ℤ)
    (C : AlgebraicClasses H p) :
    HodgeConjectureFor H p C ↔
      ∃ S : Set V, S ⊆ (C.A : Set V) ∧ Submodule.span ℚ S = hodgeClasses H p := by
  constructor
  · intro h
    exact ⟨(hodgeClasses H p : Set V), h, Submodule.span_eq _⟩
  · rintro ⟨S, hS, hspan⟩
    rw [HodgeConjectureFor, ← hspan]
    exact Submodule.span_le.2 hS

/-!
## Functoriality: transfer of the conjecture along morphisms of Hodge structures
-/

section Morphisms

variable {V' : Type} [AddCommGroup V'] [Module ℚ V']

/-- A `ℚ`-linear map `f : V → V'` is a *morphism of Hodge structures* if its
complexification carries `H^{a,b}` into `H'^{a,b}` for all `a, b`. -/
def IsHodgeMorphism {w w' : ℤ} (H : HodgeStructure V w) (H' : HodgeStructure V' w')
    (f : V →ₗ[ℚ] V') : Prop :=
  ∀ a b : ℤ, ((H.F a b).restrictScalars ℚ) ≤
    Submodule.comap (LinearMap.lTensor ℂ f) ((H'.F a b).restrictScalars ℚ)

/-- A morphism of Hodge structures carries Hodge classes to Hodge classes. -/
theorem map_hodgeClasses_le {w w' : ℤ} {H : HodgeStructure V w} {H' : HodgeStructure V' w'}
    {f : V →ₗ[ℚ] V'} (hf : IsHodgeMorphism H H' f) (p : ℤ) :
    (hodgeClasses H p).map f ≤ hodgeClasses H' p := by
  rintro _ ⟨v, hv, rfl⟩
  have h1 : (1 : ℂ) ⊗ₜ[ℚ] v ∈ H.F p p := hv
  have h2 := hf p p h1
  have h3 : (LinearMap.lTensor ℂ f) ((1 : ℂ) ⊗ₜ[ℚ] v) = (1 : ℂ) ⊗ₜ[ℚ] f v := by
    simp
  rw [Submodule.mem_comap, h3] at h2
  exact h2

/-- **Reduction along a morphism.**  If `f` is a morphism of Hodge structures whose image
already contains all Hodge classes of the target, and if it carries algebraic classes to
algebraic classes, then the Hodge conjecture for the source implies it for the target.
This is the linear-algebra content of the standard reduction of the Hodge conjecture along
correspondences (e.g. along a resolution or a hyperplane section). -/
theorem hodgeConjectureFor_of_morphism {w w' : ℤ} {H : HodgeStructure V w}
    {H' : HodgeStructure V' w'} {f : V →ₗ[ℚ] V'} {p : ℤ}
    (C : AlgebraicClasses H p) (C' : AlgebraicClasses H' p)
    (hsurj : hodgeClasses H' p ≤ (hodgeClasses H p).map f)
    (hA : C.A.map f ≤ C'.A) (hHC : HodgeConjectureFor H p C) :
    HodgeConjectureFor H' p C' := by
  intro v' hv'
  obtain ⟨v, hv, rfl⟩ := hsurj hv'
  exact hA ⟨v, hHC hv, rfl⟩

/-- If moreover every Hodge class of the target is the image of a Hodge class of the
source, then the Hodge classes of the target are exactly the images of those of the
source. -/
theorem hodgeClasses_eq_map_of_morphism {w w' : ℤ} {H : HodgeStructure V w}
    {H' : HodgeStructure V' w'} {f : V →ₗ[ℚ] V'} {p : ℤ} (hf : IsHodgeMorphism H H' f)
    (hsurj : hodgeClasses H' p ≤ (hodgeClasses H p).map f) :
    hodgeClasses H' p = (hodgeClasses H p).map f :=
  le_antisymm hsurj (map_hodgeClasses_le hf p)

end Morphisms

/-!
## Base cases
-/

/-- If the `(p,p)` piece of the Hodge decomposition vanishes, there are no nonzero Hodge
classes. -/
theorem hodgeClasses_eq_bot_of_F_eq_bot {w : ℤ} (H : HodgeStructure V w) (p : ℤ)
    (h : H.F p p = ⊥) : hodgeClasses H p = ⊥ := by
  ext v
  simp only [hodgeClasses, Submodule.mem_comap, Submodule.restrictScalars_mem, h,
    Submodule.mem_bot]
  constructor
  · intro hv
    have : (1 : ℂ) ⊗ₜ[ℚ] v = 0 := hv
    have h0 : toCx v = toCx (0 : V) := by simpa [toCx, TensorProduct.mk_apply] using this
    exact toCx_injective h0
  · rintro rfl
    simp [toCx]

/-- **Base case (wrong degree).**  If `2p ≠ w`, there is no `(p,p)`-part, hence no nonzero
Hodge class, and the Hodge conjecture holds (trivially, but genuinely). -/
theorem hodgeConjectureFor_of_two_mul_ne {w : ℤ} (H : HodgeStructure V w) (p : ℤ)
    (hpw : p + p ≠ w) (C : AlgebraicClasses H p) : HodgeConjectureFor H p C := by
  rw [HodgeConjectureFor, hodgeClasses_eq_bot_of_F_eq_bot H p (H.weight p p hpw)]
  exact bot_le

/-- The Hodge structure of *Tate type* `(p,p)`: the whole complexification sits in
bidegree `(p,p)`.  This is the Hodge structure of `H^{2p}` of, e.g., a point (`p = 0`),
or the one generated by powers of the class of a hyperplane section. -/
noncomputable def tateHodgeStructure (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    HodgeStructure V (p + p) where
  F a b := if a = p ∧ b = p then ⊤ else ⊥
  weight a b hab := by
    have : ¬ (a = p ∧ b = p) := by rintro ⟨rfl, rfl⟩; exact hab rfl
    simp [this]
  indep := by
    intro ab
    by_cases h : ab.1 = p ∧ ab.2 = p
    · have hsup : (⨆ (cd : ℤ × ℤ) (_ : cd ≠ ab), if cd.1 = p ∧ cd.2 = p then
          (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥) = ⊥ := by
        refine iSup_eq_bot.2 fun cd => iSup_eq_bot.2 fun hcd => ?_
        by_cases h' : cd.1 = p ∧ cd.2 = p
        · exact absurd (Prod.ext (h'.1.trans h.1.symm) (h'.2.trans h.2.symm)) hcd
        · simp [h']
      simp only [hsup]
      exact disjoint_bot_right
    · simp only [h, if_false]
      exact disjoint_bot_left
  spanning := by
    refine top_le_iff.1 ?_
    refine le_trans ?_ (le_iSup (fun ab : ℤ × ℤ =>
      if ab.1 = p ∧ ab.2 = p then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥) (p, p))
    simp
  conj_symm a b := by
    by_cases h : a = p ∧ b = p
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true]
      rw [Submodule.restrictScalars_top, Submodule.map_top,
        LinearMap.range_eq_top.2 (conjC_surjective V)]
    · have h' : ¬ (b = p ∧ a = p) := fun hb => h ⟨hb.2, hb.1⟩
      simp [h, h']

@[simp] theorem tateHodgeStructure_F_self (V : Type) [AddCommGroup V] [Module ℚ V]
    (p : ℤ) : (tateHodgeStructure V p).F p p = ⊤ := by
  simp [tateHodgeStructure]

/-- **Base case (Tate type).**  For a Hodge structure of type `(p,p)` every rational class
is a Hodge class. -/
theorem hodgeClasses_tate (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ) :
    hodgeClasses (tateHodgeStructure V p) p = ⊤ := by
  ext v
  simp [hodgeClasses]

/-- **Base case (degree `0`).**  For a connected smooth projective variety, `H^0(X, ℚ) = ℚ`
carries the Tate Hodge structure of weight `0`, every class is a Hodge class, and the
algebraic classes are all of `H^0` (spanned by the fundamental class `[X]`).  The Hodge
conjecture therefore holds in degree `0`. -/
theorem hodgeConjectureFor_degree_zero
    (C : AlgebraicClasses (tateHodgeStructure ℚ 0) 0) (hC : C.A = ⊤) :
    HodgeConjectureFor (tateHodgeStructure ℚ 0) 0 C := by
  rw [HodgeConjectureFor, hC]
  exact le_top

/-- The degree-`0` datum really exists: the fundamental class spans `H^0`, and it is a
Hodge class.  (This shows the base case above is not vacuous.) -/
noncomputable def degreeZeroAlgebraicClasses : AlgebraicClasses (tateHodgeStructure ℚ 0) 0 where
  A := ⊤
  alg_le_hodge := by rw [hodgeClasses_tate]

/-!
## The target statement
-/

/-- **The Hodge conjecture, formalized, together with a Lean-checked reduction and the
proved base cases.**

The conjunction below states, for every rational Hodge structure `H` of weight `w` on a
ℚ-vector space `V`, every `p`, and every space `C` of algebraic cycle classes:

1. the *contrapositive* reformulation: the conjecture for `(H, p, C)` holds iff there is
   no Hodge class outside the algebraic classes;
2. the reformulation as an *equality* `hodgeClasses = algebraic classes` (using that
   algebraic classes are Hodge classes);
3. the reduction to a *spanning family*: the conjecture holds iff the Hodge classes are
   spanned by algebraic classes;
4. the base case `p + p ≠ w`: there are no nonzero Hodge classes of type `(p,p)`, so the
   conjecture holds;
5. the base case of a Hodge structure of Tate type `(p,p)`: all rational classes are
   Hodge classes;
6. the base case of degree `0`: for `H^0(X,ℚ) = ℚ` with its weight-`0` Tate Hodge
   structure and the algebraic classes spanned by the fundamental class, the conjecture
   holds.
-/
theorem hodge_statement :
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ)
        (C : AlgebraicClasses H p),
        HodgeConjectureFor H p C ↔ ¬ ∃ v : V, v ∈ hodgeClasses H p ∧ v ∉ C.A) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ)
        (C : AlgebraicClasses H p),
        HodgeConjectureFor H p C ↔ hodgeClasses H p = C.A) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ)
        (C : AlgebraicClasses H p),
        HodgeConjectureFor H p C ↔
          ∃ S : Set V, S ⊆ (C.A : Set V) ∧ Submodule.span ℚ S = hodgeClasses H p) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) (H : HodgeStructure V w) (p : ℤ),
        p + p ≠ w → hodgeClasses H p = ⊥ ∧
          ∀ C : AlgebraicClasses H p, HodgeConjectureFor H p C) ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℚ V] (p : ℤ),
        hodgeClasses (tateHodgeStructure V p) p = ⊤) ∧
    (∀ C : AlgebraicClasses (tateHodgeStructure ℚ 0) 0, C.A = ⊤ →
        HodgeConjectureFor (tateHodgeStructure ℚ 0) 0 C) ∧
    (∀ (V V' : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
        (w w' : ℤ) (H : HodgeStructure V w) (H' : HodgeStructure V' w') (p : ℤ)
        (f : V →ₗ[ℚ] V'), IsHodgeMorphism H H' f →
          (hodgeClasses H p).map f ≤ hodgeClasses H' p) ∧
    (∀ (V V' : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']
        (w w' : ℤ) (H : HodgeStructure V w) (H' : HodgeStructure V' w') (p : ℤ)
        (f : V →ₗ[ℚ] V') (C : AlgebraicClasses H p) (C' : AlgebraicClasses H' p),
        hodgeClasses H' p ≤ (hodgeClasses H p).map f → C.A.map f ≤ C'.A →
          HodgeConjectureFor H p C → HodgeConjectureFor H' p C') := by
  refine ⟨fun V _ _ w H p C => hodgeConjectureFor_iff_not_exists H p C,
    fun V _ _ w H p C => hodgeConjectureFor_iff_eq H p C,
    fun V _ _ w H p C => hodgeConjectureFor_iff_span H p C,
    fun V _ _ w H p hpw =>
      ⟨hodgeClasses_eq_bot_of_F_eq_bot H p (H.weight p p hpw),
        fun C => hodgeConjectureFor_of_two_mul_ne H p hpw C⟩,
    fun V _ _ p => hodgeClasses_tate V p,
    fun C hC => hodgeConjectureFor_degree_zero C hC,
    fun V V' _ _ _ _ w w' H H' p f hf => map_hodgeClasses_le hf p,
    fun V V' _ _ _ _ w w' H H' p f C C' hsurj hA hHC =>
      hodgeConjectureFor_of_morphism C C' hsurj hA hHC⟩

end Frontier

