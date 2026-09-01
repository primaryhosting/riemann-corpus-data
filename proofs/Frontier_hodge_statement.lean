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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open TensorProduct

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a rational vector
space `V` (conjugation on the left factor, identity on `V`).  It is only `ℚ`-linear
(it is conjugate-linear over `ℂ`). -/
noncomputable def cxConj (V : Type) [AddCommGroup V] [Module ℚ V] :
    (ℂ ⊗[ℚ] V) →ₗ[ℚ] (ℂ ⊗[ℚ] V) :=
  TensorProduct.map (Complex.conjAe.toAlgHom.restrictScalars ℚ).toLinearMap LinearMap.id

/-- A (pure) rational Hodge structure of weight `w` on a `ℚ`-vector space `V`:
a decomposition of the complexification `V ⊗ ℂ` into subspaces `H^{p,q}` with
`p + q = w`, which is a direct sum decomposition and is exchanged by complex
conjugation, `conj (H^{p,q}) = H^{q,p}`. -/
structure HodgeStructure (V : Type) [AddCommGroup V] [Module ℚ V] (w : ℤ) where
  /-- The `(p,q)`-piece of the Hodge decomposition of `ℂ ⊗[ℚ] V`. -/
  piece : ℤ → ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Only bidegrees of total degree `w` occur. -/
  weight : ∀ p q : ℤ, p + q ≠ w → piece p q = ⊥
  /-- The pieces span the complexification. -/
  span_eq_top : (⨆ p : ℤ, ⨆ q : ℤ, piece p q) = ⊤
  /-- The pieces are independent, so the sum is direct. -/
  indep : iSupIndep fun pq : ℤ × ℤ => piece pq.1 pq.2
  /-- Complex conjugation exchanges `H^{p,q}` and `H^{q,p}`. -/
  conj_piece : ∀ (p q : ℤ) (x : ℂ ⊗[ℚ] V), x ∈ piece p q → cxConj V x ∈ piece q p

variable {H : ℕ → Type} [∀ p, AddCommGroup (H p)] [∀ p, Module ℚ (H p)]

/-- The cohomological data of a smooth complex projective variety that enters the
statement of the Hodge conjecture.

`H p` plays the role of the singular cohomology group `H^{2p}(X, ℚ)`; it carries a
rational Hodge structure of weight `2p`.  `alg p` is the `ℚ`-subspace spanned by the
cycle classes of codimension-`p` algebraic subvarieties of `X`; cycle classes are of
type `(p,p)`, which is the field `alg_isHodge`.

The two remaining fields record the standard normalisations for a connected variety:
`H^0(X, ℚ)` is purely of type `(0,0)` and is spanned by the fundamental class of `X`,
which is algebraic. -/
structure HodgeVariety (H : ℕ → Type) [∀ p, AddCommGroup (H p)] [∀ p, Module ℚ (H p)] where
  /-- The weight-`2p` Hodge structure on `H^{2p}(X, ℚ)`. -/
  hs : ∀ p : ℕ, HodgeStructure (H p) (2 * p)
  /-- The span of the classes of codimension-`p` algebraic cycles. -/
  alg : ∀ p : ℕ, Submodule ℚ (H p)
  /-- Algebraic cycle classes are of type `(p,p)`. -/
  alg_isHodge : ∀ (p : ℕ) (v : H p), v ∈ alg p → (1 : ℂ) ⊗ₜ[ℚ] v ∈ (hs p).piece p p
  /-- `H^0(X, ℚ)` is purely of type `(0,0)`. -/
  degree_zero_type : (hs 0).piece 0 0 = ⊤
  /-- `H^0(X, ℚ)` is spanned by the (algebraic) fundamental class of `X`. -/
  alg_degree_zero : alg 0 = ⊤

/-- The space of *Hodge classes* of codimension `p`: rational classes in `H^{2p}(X, ℚ)`
whose image in `H^{2p}(X, ℂ)` lies in the `(p,p)`-part of the Hodge decomposition. -/
noncomputable def hodgeClasses (X : HodgeVariety H) (p : ℕ) : Submodule ℚ (H p) :=
  Submodule.comap (TensorProduct.mk ℚ ℂ (H p) 1) (((X.hs p).piece p p).restrictScalars ℚ)

@[simp] lemma mem_hodgeClasses {X : HodgeVariety H} {p : ℕ} {v : H p} :
    v ∈ hodgeClasses X p ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs p).piece p p := Iff.rfl

/-- The Hodge conjecture in codimension `p` for `X`: every Hodge class of codimension `p`
is a rational linear combination of classes of algebraic cycles. -/
def HodgeConjectureAt (X : HodgeVariety H) (p : ℕ) : Prop :=
  X.alg p = hodgeClasses X p

/-- The Hodge conjecture for `X`: in every codimension, the Hodge classes are exactly the
rational combinations of algebraic cycle classes. -/
def HodgeConjecture (X : HodgeVariety H) : Prop :=
  ∀ p : ℕ, HodgeConjectureAt X p

/-- One inclusion always holds: algebraic cycle classes are Hodge classes. -/
theorem alg_le_hodgeClasses (X : HodgeVariety H) (p : ℕ) :
    X.alg p ≤ hodgeClasses X p := fun _ hv => X.alg_isHodge p _ hv

/-- Contrapositive reformulation: the Hodge conjecture in codimension `p` holds iff there
is no non-algebraic Hodge class of codimension `p`. -/
theorem hodgeConjectureAt_iff_no_nonalgebraic (X : HodgeVariety H) (p : ℕ) :
    HodgeConjectureAt X p ↔ ¬ ∃ v : H p, v ∈ hodgeClasses X p ∧ v ∉ X.alg p := by
  constructor
  · rintro h ⟨v, hv, hv'⟩
    exact hv' (h ▸ hv)
  · intro h
    refine le_antisymm (alg_le_hodgeClasses X p) fun v hv => ?_
    by_contra hv'
    exact h ⟨v, hv, hv'⟩

/-- Equivalent "surjectivity" form of the whole conjecture. -/
theorem hodgeConjecture_iff (X : HodgeVariety H) :
    HodgeConjecture X ↔ ∀ p : ℕ, hodgeClasses X p ≤ X.alg p := by
  constructor
  · intro h p
    exact (h p).ge
  · intro h p
    exact le_antisymm (alg_le_hodgeClasses X p) (h p)

/-- If the `(p,p)`-part of the Hodge decomposition vanishes, then there are no nonzero
Hodge classes of codimension `p`. -/
theorem hodgeClasses_eq_bot_of_piece_eq_bot (X : HodgeVariety H) (p : ℕ)
    (hp : (X.hs p).piece p p = ⊥) : hodgeClasses X p = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  have hv' : (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs p).piece p p := hv
  rw [hp, Submodule.mem_bot] at hv'
  have hinj : Function.Injective ((TensorProduct.mk ℚ ℂ (H p)) 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (H p)
  have : v = 0 := by
    have h0 : ((TensorProduct.mk ℚ ℂ (H p)) 1) v = ((TensorProduct.mk ℚ ℂ (H p)) 1) 0 := by
      simpa using hv'
    exact hinj h0
  simp [this]

/-- Vanishing case of the Hodge conjecture: if `H^{p,p} = 0` then the conjecture holds in
codimension `p` (both sides are zero). -/
theorem hodgeConjectureAt_of_piece_eq_bot (X : HodgeVariety H) (p : ℕ)
    (hp : (X.hs p).piece p p = ⊥) : HodgeConjectureAt X p := by
  have hb := hodgeClasses_eq_bot_of_piece_eq_bot X p hp
  have hle := alg_le_hodgeClasses X p
  rw [hb] at hle
  rw [HodgeConjectureAt, hb, le_bot_iff.mp hle]

/-- Base case of the Hodge conjecture: it holds in codimension `0`, where every class is a
Hodge class and every class is a rational multiple of the fundamental class. -/
theorem hodgeConjectureAt_zero (X : HodgeVariety H) : HodgeConjectureAt X 0 := by
  have h : hodgeClasses X 0 = ⊤ := by
    refine le_antisymm le_top fun v _ => ?_
    show (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs 0).piece 0 0
    rw [X.degree_zero_type]
    exact Submodule.mem_top
  rw [HodgeConjectureAt, h, X.alg_degree_zero]

/-- **The Hodge conjecture, stated, together with the Lean-checked reductions and base
cases that are proved here.**

For every smooth complex projective variety `X` (represented by its cohomological Hodge
data), the *Hodge conjecture* asserts

  `HodgeConjecture X : ∀ p, X.alg p = hodgeClasses X p`,

i.e. every rational cohomology class of type `(p,p)` is a rational linear combination of
classes of algebraic cycles.  The statement below records:

1. the always-valid inclusion: algebraic classes are Hodge classes;
2. the contrapositive reformulation in each codimension: the conjecture holds in
   codimension `p` iff no Hodge class fails to be algebraic;
3. the global reduction of the conjecture to the single inclusion
   `hodgeClasses X p ≤ X.alg p`;
4. the base case `p = 0`, which is proved unconditionally;
5. the vanishing case: whenever `H^{p,p} = 0`, the conjecture holds in codimension `p`. -/
theorem hodge_statement :
    ∀ {H : ℕ → Type} [∀ p, AddCommGroup (H p)] [∀ p, Module ℚ (H p)]
      (X : HodgeVariety H),
      (∀ p : ℕ, X.alg p ≤ hodgeClasses X p) ∧
      (∀ p : ℕ, HodgeConjectureAt X p ↔ ¬ ∃ v : H p, v ∈ hodgeClasses X p ∧ v ∉ X.alg p) ∧
      (HodgeConjecture X ↔ ∀ p : ℕ, hodgeClasses X p ≤ X.alg p) ∧
      HodgeConjectureAt X 0 ∧
      (∀ p : ℕ, (X.hs p).piece p p = ⊥ → HodgeConjectureAt X p) := by
  intro H _ _ X
  exact ⟨alg_le_hodgeClasses X, hodgeConjectureAt_iff_no_nonalgebraic X,
    hodgeConjecture_iff X, hodgeConjectureAt_zero X,
    fun p hp => hodgeConjectureAt_of_piece_eq_bot X p hp⟩

end Frontier

