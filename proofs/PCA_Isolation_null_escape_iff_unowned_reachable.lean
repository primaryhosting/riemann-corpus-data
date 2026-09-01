/-
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

variable {α : Type*}

/-- An *isolate*: the abstract model used by the isolation engine.

* `edge a b` means the object `a` holds a reference to the object `b`;
* `owned` is the set of objects that belong to (are owned by) the isolate;
* `root` is the isolate's entry object.
-/
structure Isolate (α : Type*) where
  /-- `edge a b` holds when object `a` stores a reference to object `b`. -/
  edge : α → α → Prop
  /-- The set of objects owned by the isolate. -/
  owned : Set α
  /-- The entry object of the isolate. -/
  root : α

/-- `Reaches I a b` : `b` is reachable from `a` by following references. -/
def Reaches (I : Isolate α) : α → α → Prop :=
  Relation.ReflTransGen I.edge

/-- A *null escape trace* is the concrete counterexample the engine produces: a finite
reference trace `root :: l` all of whose consecutive steps are references, whose final
object is **not** owned by the isolate (so the null reference travelling along the trace
leaves the isolate). -/
def EscapeTrace (I : Isolate α) (l : List α) : Prop :=
  List.IsChain I.edge (I.root :: l) ∧
    (I.root :: l).getLast (List.cons_ne_nil _ _) ∉ I.owned

/-- A null reference escapes the isolate when some escape trace exists. -/
def NullEscape (I : Isolate α) : Prop :=
  ∃ l : List α, EscapeTrace I l

/-- **Soundness and completeness of the isolation engine's model.**
A null reference escapes the isolate (i.e. the engine can exhibit a reference trace out of
the isolate) if and only if some object that is not owned by the isolate is reachable from
its root.

The two directions are exactly Mathlib's correspondence between `Relation.ReflTransGen` and
finite chains, `List.exists_isChain_cons_of_relationReflTransGen` and
`List.relationReflTransGen_of_exists_isChain_cons`. -/
theorem null_escape_iff_unowned_reachable (I : Isolate α) :
    NullEscape I ↔ ∃ n, Reaches I I.root n ∧ n ∉ I.owned := by
  constructor
  · rintro ⟨l, hchain, hlast⟩
    exact ⟨_, List.relationReflTransGen_of_exists_isChain_cons l hchain rfl, hlast⟩
  · rintro ⟨n, hreach, hn⟩
    obtain ⟨l, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen (r := I.edge) hreach
    exact ⟨l, hchain, by rw [hlast]; exact hn⟩

/-- **Soundness.** If every object reachable from the root is owned by the isolate, then no
null reference can escape it. -/
theorem not_nullEscape_of_forall_reachable_owned (I : Isolate α)
    (h : ∀ n, Reaches I I.root n → n ∈ I.owned) : ¬ NullEscape I := by
  rw [null_escape_iff_unowned_reachable]
  rintro ⟨n, hreach, hn⟩
  exact hn (h n hreach)

/-- **Completeness.** If some unowned object is reachable, the engine can exhibit an escape
trace. -/
theorem nullEscape_of_unowned_reachable (I : Isolate α) {n : α}
    (hreach : Reaches I I.root n) (hn : n ∉ I.owned) : NullEscape I :=
  (null_escape_iff_unowned_reachable I).2 ⟨n, hreach, hn⟩

/-- If the root itself is not owned, a null reference escapes immediately. -/
theorem nullEscape_of_root_not_owned (I : Isolate α) (h : I.root ∉ I.owned) :
    NullEscape I :=
  nullEscape_of_unowned_reachable I Relation.ReflTransGen.refl h

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

