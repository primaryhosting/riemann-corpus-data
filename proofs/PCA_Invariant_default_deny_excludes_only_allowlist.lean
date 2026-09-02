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
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

/-- The decision produced by the isolation engine for a requested capability. -/
inductive Decision
  | permit
  | deny
  deriving DecidableEq, Repr

/-- A policy of the isolation engine: an allowlist of capabilities (given as a predicate on
capabilities) together with a flag saying whether the residual, non-allowlisted behaviour is
*default deny*. -/
structure Policy (Cap : Type _) where
  /-- The predicate describing the explicitly allowed capabilities. -/
  allow : Cap → Prop
  /-- Whether capabilities outside the allowlist are denied. -/
  defaultDeny : Bool

/-- The engine's decision procedure: an allowlisted capability is permitted; anything else is
denied exactly when the policy is in default-deny mode. -/
noncomputable def Policy.eval {Cap : Type _} (p : Policy Cap) (c : Cap) : Decision :=
  open Classical in
  if p.allow c then Decision.permit
  else if p.defaultDeny then Decision.deny else Decision.permit

/-- The predicate describing the capabilities the engine denies. -/
noncomputable def Policy.denied {Cap : Type _} (p : Policy Cap) : Cap → Prop :=
  fun c => p.eval c = Decision.deny

namespace Invariant

/-- **Default deny excludes only the allowlist.**

For a policy in default-deny mode the isolation engine is both *sound* — it permits exactly the
allowlisted capabilities, so nothing outside the allowlist ever slips through — and *complete*:
it denies every capability that is not on the allowlist.  Equivalently, the denied predicate is
literally the negation of the allowlist predicate, i.e. default deny excludes only (and all of)
the complement of the allowlist. -/
theorem default_deny_excludes_only_allowlist {Cap : Type _} (p : Policy Cap)
    (hp : p.defaultDeny = true) :
    (∀ c : Cap, p.eval c = Decision.deny ↔ ¬ p.allow c) ∧
      (∀ c : Cap, p.eval c = Decision.permit ↔ p.allow c) ∧
      p.denied = fun c => ¬ p.allow c := by
  have key : ∀ c : Cap,
      (p.eval c = Decision.deny ↔ ¬ p.allow c) ∧
        (p.eval c = Decision.permit ↔ p.allow c) := by
    intro c
    rcases Classical.em (p.allow c) with hc | hc
    · have h : p.eval c = Decision.permit := by
        simp [Policy.eval, hc]
      exact ⟨by simp [h, hc], by simp [h, hc]⟩
    · have h : p.eval c = Decision.deny := by
        simp [Policy.eval, hc, hp]
      exact ⟨by simp [h, hc], by simp [h, hc]⟩
  refine ⟨fun c => (key c).1, fun c => (key c).2, ?_⟩
  funext c
  exact propext (key c).1

end Invariant

end PCA

