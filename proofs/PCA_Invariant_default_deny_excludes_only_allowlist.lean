/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Invariant

/-- Principals of the isolation engine: either a root principal, or a principal
obtained by delegation from a parent principal. -/
inductive Principal where
  | root (name : String)
  | delegate (parent : Principal) (name : String)
  deriving DecidableEq

/-- A policy assigns to each principal the allowlist of capabilities that this
principal explicitly grants, as a decidable predicate on capabilities. -/
abbrev Policy (Cap : Type) := Principal → Cap → Bool

variable {Cap : Type}

/-- The delegation chain of a principal: the principal itself together with all
of its ancestors. -/
def chain : Principal → List Principal
  | .root n => [.root n]
  | .delegate p n => .delegate p n :: chain p

/-- The decision procedure of the isolation engine.  Access is *denied by
default*: it is granted only when the requested capability appears on the
allowlist of the principal itself and, recursively, on the allowlist of the
delegating parent (delegation attenuates). -/
def granted (pol : Policy Cap) : Principal → Cap → Bool
  | .root n, c => pol (.root n) c
  | .delegate p n, c => pol (.delegate p n) c && granted pol p c

/-- The effective allowlist of a principal: the capabilities allowed by every
principal on its delegation chain. -/
def effectiveAllow (pol : Policy Cap) (pr : Principal) (c : Cap) : Prop :=
  ∀ q ∈ chain pr, pol q c = true

/-- Soundness and completeness of the engine with respect to the effective
allowlist: the engine grants exactly the effective allowlist. -/
theorem granted_iff_effectiveAllow (pol : Policy Cap) (pr : Principal) (c : Cap) :
    granted pol pr c = true ↔ effectiveAllow pol pr c := by
  induction pr with
  | root n => simp [granted, effectiveAllow, chain]
  | delegate p n ih =>
      simp only [granted, effectiveAllow, chain, Bool.and_eq_true, List.mem_cons,
        forall_eq_or_imp] at *
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ih.mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ih.mpr h2⟩

/-- **Default deny excludes only the allowlist.**  A request is denied by the
isolation engine exactly when the requested capability is *not* in the effective
allowlist of the requesting principal: nothing on the allowlist is ever denied,
and everything off it is denied. -/
theorem default_deny_excludes_only_allowlist (pol : Policy Cap) (pr : Principal) (c : Cap) :
    granted pol pr c = false ↔ ¬ effectiveAllow pol pr c := by
  rw [← granted_iff_effectiveAllow, Bool.not_eq_true]

/-- The denied set is exactly the complement of the effective allowlist. -/
theorem denied_eq_compl_effectiveAllow (pol : Policy Cap) (pr : Principal) :
    (fun c : Cap => granted pol pr c = false) = fun c : Cap => ¬ effectiveAllow pol pr c := by
  funext c
  exact propext (default_deny_excludes_only_allowlist pol pr c)

/-- Under the empty policy everything is denied: the engine really is default
deny. -/
theorem granted_empty_policy (pr : Principal) (c : Cap) :
    granted (fun _ _ => false) pr c = false := by
  induction pr with
  | root n => simp [granted]
  | delegate p n ih => simp [granted, ih]

/-- Delegation only attenuates: a delegate never holds a capability its parent
lacks. -/
theorem granted_delegate_le_parent (pol : Policy Cap) (p : Principal) (n : String) (c : Cap)
    (h : granted pol (.delegate p n) c = true) : granted pol p c = true := by
  simpa [granted] using ((Bool.and_eq_true _ _).mp h).2

end PCA.Invariant

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

