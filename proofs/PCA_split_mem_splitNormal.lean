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

/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace PCA
namespace Isolation

/-- Policy conditions of the isolation engine: propositional formulas over
abstract atoms `α` (e.g. capability / resource predicates on a state). -/
inductive Cond (α : Type u) : Type _
  | atom : α → Cond α
  | tru : Cond α
  | fls : Cond α
  | neg : Cond α → Cond α
  | conj : Cond α → Cond α → Cond α
  | disj : Cond α → Cond α → Cond α
  deriving Repr

namespace Cond

variable {α : Type u}

/-- Semantics of a policy condition relative to a valuation of atoms. -/
def eval (v : α → Prop) : Cond α → Prop
  | .atom a => v a
  | .tru => True
  | .fls => False
  | .neg p => ¬ eval v p
  | .conj p q => eval v p ∧ eval v q
  | .disj p q => eval v p ∨ eval v q

/-- A condition is *split-normal* when no disjunction occurs positively
(i.e. outside of a negation): these are exactly the shapes the isolation
engine handles as a single branch. -/
def SplitNormal : Cond α → Prop
  | .atom _ => True
  | .tru => True
  | .fls => True
  | .neg _ => True
  | .conj p q => SplitNormal p ∧ SplitNormal q
  | .disj _ _ => False

/-- The disjunction split of the isolation engine: a condition is compiled into
a finite list of branches, obtained by distributing conjunction over
disjunction. -/
def split : Cond α → List (Cond α)
  | .atom a => [.atom a]
  | .tru => [.tru]
  | .fls => [.fls]
  | .neg p => [.neg p]
  | .disj p q => split p ++ split q
  | .conj p q => (split p).flatMap fun a => (split q).map fun b => .conj a b

@[simp] theorem split_atom (a : α) : split (.atom a) = [.atom a] := rfl
@[simp] theorem split_tru : split (α := α) .tru = [.tru] := rfl
@[simp] theorem split_fls : split (α := α) .fls = [.fls] := rfl
@[simp] theorem split_neg (p : Cond α) : split (.neg p) = [.neg p] := rfl
@[simp] theorem split_disj (p q : Cond α) : split (.disj p q) = split p ++ split q := rfl
@[simp] theorem split_conj (p q : Cond α) :
    split (.conj p q) = (split p).flatMap (fun a => (split q).map fun b => .conj a b) := rfl

end Cond

open Cond

variable {α : Type u}

/-- Every branch produced by the disjunction split is split-normal:
the split really does isolate the disjunctive structure. -/
theorem split_mem_splitNormal :
    ∀ (c : Cond α), ∀ b ∈ Cond.split c, Cond.SplitNormal b := by
  intro c
  induction c with
  | atom a => intro b hb; simp at hb; subst hb; trivial
  | tru => intro b hb; simp at hb; subst hb; trivial
  | fls => intro b hb; simp at hb; subst hb; trivial
  | neg p => intro b hb; simp at hb; subst hb; trivial
  | disj p q ihp ihq =>
      intro b hb
      rcases List.mem_append.1 (by simpa using hb) with h | h
      · exact ihp b h
      · exact ihq b h
  | conj p q ihp ihq =>
      intro b hb
      simp only [Cond.split_conj, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨x, hx, y, hy, rfl⟩ := hb
      exact ⟨ihp x hx, ihq y hy⟩

/-- **Disjunction split preserves semantics.**
A valuation satisfies a policy condition iff it satisfies one of the branches
produced by the isolation engine's disjunction split. -/
theorem disjunction_split_preserves_semantics (v : α → Prop) (c : Cond α) :
    Cond.eval v c ↔ ∃ b ∈ Cond.split c, Cond.eval v b := by
  induction c with
  | atom a => simp [Cond.eval]
  | tru => simp [Cond.eval]
  | fls => simp [Cond.eval]
  | neg p => simp [Cond.eval]
  | disj p q ihp ihq =>
      constructor
      · rintro (h | h)
        · obtain ⟨b, hb, hbv⟩ := ihp.1 h
          exact ⟨b, by simp [List.mem_append, hb], hbv⟩
        · obtain ⟨b, hb, hbv⟩ := ihq.1 h
          exact ⟨b, by simp [List.mem_append, hb], hbv⟩
      · rintro ⟨b, hb, hbv⟩
        rcases List.mem_append.1 (by simpa using hb) with h | h
        · exact Or.inl (ihp.2 ⟨b, h, hbv⟩)
        · exact Or.inr (ihq.2 ⟨b, h, hbv⟩)
  | conj p q ihp ihq =>
      constructor
      · rintro ⟨hp, hq⟩
        obtain ⟨x, hx, hxv⟩ := ihp.1 hp
        obtain ⟨y, hy, hyv⟩ := ihq.1 hq
        refine ⟨Cond.conj x y, ?_, ⟨hxv, hyv⟩⟩
        simp only [Cond.split_conj, List.mem_flatMap, List.mem_map]
        exact ⟨x, hx, y, hy, rfl⟩
      · rintro ⟨b, hb, hbv⟩
        simp only [Cond.split_conj, List.mem_flatMap, List.mem_map] at hb
        obtain ⟨x, hx, y, hy, rfl⟩ := hb
        obtain ⟨hxv, hyv⟩ := hbv
        exact ⟨ihp.2 ⟨x, hx, hxv⟩, ihq.2 ⟨y, hy, hyv⟩⟩

/-- Soundness direction: any branch that is satisfied witnesses satisfaction of
the original policy condition. -/
theorem split_sound (v : α → Prop) (c : Cond α) {b : Cond α}
    (hb : b ∈ Cond.split c) (hbv : Cond.eval v b) : Cond.eval v c :=
  (disjunction_split_preserves_semantics v c).2 ⟨b, hb, hbv⟩

/-- Completeness direction: every satisfying valuation of a policy condition
satisfies some branch of its disjunction split. -/
theorem split_complete (v : α → Prop) (c : Cond α) (h : Cond.eval v c) :
    ∃ b ∈ Cond.split c, Cond.eval v b :=
  (disjunction_split_preserves_semantics v c).1 h

end Isolation
end PCA

