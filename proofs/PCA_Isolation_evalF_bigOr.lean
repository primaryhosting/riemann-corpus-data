import Mathlib

/-!
# A formal model of an isolation engine's scope decision procedure

This file gives a self-contained formal model of the *isolation engine* used to decide
whether a resource is "in scope" for a given isolation scope, together with the
soundness **and** completeness statement for the boolean *encoding* the engine actually
evaluates.

## The model

* Resources are identified by hierarchical **labels** (`PCA.Isolation.Label`), i.e. paths
  in a naming tree, represented as lists of path components.
* An isolation **scope** (`PCA.Isolation.Scope`) is given by a list of *allow roots* and a
  list of *deny roots*.
* The **semantics** (`PCA.Isolation.InScope`) says: a label is in scope iff some allow root
  is a prefix of it and no deny root is a prefix of it.
* The engine does not evaluate this semantics directly.  It *compiles* a scope into a
  propositional formula (`PCA.Isolation.Formula`) over prefix-test atoms
  (`PCA.Isolation.encodeScope`), and evaluates that formula against the atom valuation
  induced by the resource label (`PCA.Isolation.prefixEnv`).

The main theorem `PCA.Isolation.in_scope_encoding_sound` states that this compilation is
both sound and complete: the compiled formula evaluates to `true` exactly on the labels
that are semantically in scope.
-/

namespace PCA.Isolation

/-- A hierarchical resource label: a path in the naming tree. -/
abbrev Label := List String

/-- An isolation scope: a list of allow roots together with a list of deny roots. -/
structure Scope where
  /-- Roots granting access to their whole subtree. -/
  allow : List Label
  /-- Roots revoking access to their whole subtree, overriding `allow`. -/
  deny : List Label
  deriving Repr, DecidableEq

/-- Semantics of a scope: `x` is in scope when it lies under some allow root and under no
deny root. -/
def InScope (s : Scope) (x : Label) : Prop :=
  (∃ r ∈ s.allow, r <+: x) ∧ ∀ e ∈ s.deny, ¬ (e <+: x)

/-- Propositional formulas over atoms of type `α`; the intermediate representation the
isolation engine evaluates. -/
inductive Formula (α : Type) where
  | tt : Formula α
  | ff : Formula α
  | atom : α → Formula α
  | neg : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  deriving Repr

/-- Evaluation of a formula under a valuation of atoms. -/
def evalF {α : Type} (v : α → Bool) : Formula α → Bool
  | .tt => true
  | .ff => false
  | .atom a => v a
  | .neg f => !(evalF v f)
  | .conj f g => (evalF v f) && (evalF v g)
  | .disj f g => (evalF v f) || (evalF v g)

/-- Disjunction of a list of formulas. -/
def bigOr {α : Type} : List (Formula α) → Formula α
  | [] => .ff
  | f :: fs => .disj f (bigOr fs)

/-- The compiled form of a scope: a formula whose atoms are prefix tests against the
allow and deny roots. -/
def encodeScope (s : Scope) : Formula Label :=
  .conj (bigOr (s.allow.map Formula.atom)) (.neg (bigOr (s.deny.map Formula.atom)))

/-- The atom valuation induced by a resource label: atom `r` holds iff `r` is a prefix
of the label. -/
def prefixEnv (x : Label) : Label → Bool := fun r => decide (r <+: x)

lemma evalF_bigOr {α : Type} (v : α → Bool) (fs : List (Formula α)) :
    evalF v (bigOr fs) = true ↔ ∃ f ∈ fs, evalF v f = true := by
  induction fs with
  | nil => simp [bigOr, evalF]
  | cons f fs ih => simp [bigOr, evalF, ih]

lemma evalF_bigOr_atoms (x : Label) (rs : List Label) :
    evalF (prefixEnv x) (bigOr (rs.map Formula.atom)) = true ↔ ∃ r ∈ rs, r <+: x := by
  rw [evalF_bigOr]
  simp [evalF, prefixEnv]

/-- **Soundness and completeness of the isolation engine's scope encoding.**

The propositional formula obtained by compiling a scope evaluates to `true` under the
prefix-test valuation of a resource label if and only if that label is semantically in
scope. -/
theorem in_scope_encoding_sound (s : Scope) (x : Label) :
    evalF (prefixEnv x) (encodeScope s) = true ↔ InScope s x := by
  simp only [encodeScope, evalF, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    InScope]
  rw [evalF_bigOr_atoms]
  constructor
  · rintro ⟨ha, hd⟩
    refine ⟨ha, ?_⟩
    intro e he hex
    have : evalF (prefixEnv x) (bigOr (s.deny.map Formula.atom)) = true := by
      rw [evalF_bigOr_atoms]; exact ⟨e, he, hex⟩
    rw [hd] at this; exact Bool.noConfusion this
  · rintro ⟨ha, hd⟩
    refine ⟨ha, ?_⟩
    have : ¬ (evalF (prefixEnv x) (bigOr (s.deny.map Formula.atom)) = true) := by
      rw [evalF_bigOr_atoms]
      rintro ⟨e, he, hex⟩
      exact hd e he hex
    simpa using this

/-- Membership in a scope is decidable, and decided by evaluating the compiled formula. -/
instance instDecidableInScope (s : Scope) (x : Label) : Decidable (InScope s x) :=
  decidable_of_iff _ (in_scope_encoding_sound s x)

/-- The encoding is *monotone in the allow list*: enlarging the allow roots can only
enlarge the set of accepted labels. -/
theorem in_scope_mono_allow {s t : Scope} (hs : s.allow ⊆ t.allow) (ht : t.deny = s.deny)
    (x : Label) (h : InScope s x) : InScope t x := by
  obtain ⟨⟨r, hr, hrx⟩, hd⟩ := h
  exact ⟨⟨r, hs hr, hrx⟩, by rw [ht]; exact hd⟩

/-- **Isolation theorem.**  If every allow root of `t` lies under some deny root of `s`,
then no resource can be in both scopes: the two scopes are provably isolated. -/
theorem scopes_isolated {s t : Scope}
    (h : ∀ r ∈ t.allow, ∃ e ∈ s.deny, e <+: r) (x : Label) :
    ¬ (InScope s x ∧ InScope t x) := by
  rintro ⟨⟨_, hsd⟩, ⟨⟨r, hr, hrx⟩, _⟩⟩
  obtain ⟨e, he, her⟩ := h r hr
  exact hsd e he (her.trans hrx)

end PCA.Isolation

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

