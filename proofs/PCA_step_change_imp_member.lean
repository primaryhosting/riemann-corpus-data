import Mathlib

/-!
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace PCA
namespace WriteIntegrity

universe u v w x

/-- A write request: a principal asks to store `value` at `resource`. -/
structure Request (Principal : Type u) (Resource : Type v) (Value : Type w) where
  /-- The principal issuing the write. -/
  principal : Principal
  /-- The resource being written to. -/
  resource : Resource
  /-- The value to be written. -/
  value : Value

/-- The isolation environment: every resource belongs to exactly one tenant, and
`member p t` says that principal `p` is a member of tenant `t`. -/
structure Env (Tenant : Type x) (Principal : Type u) (Resource : Type v) where
  /-- The (unique) tenant owning a resource. -/
  tenantOf : Resource → Tenant
  /-- Tenant membership relation for principals. -/
  member : Principal → Tenant → Prop

variable {Tenant : Type x} {Principal : Type u} {Resource : Type v} {Value : Type w}

/-- The guard used by the engine: a write is authorized exactly when the issuing
principal is a member of the tenant owning the target resource. -/
def Authorized (E : Env Tenant Principal Resource)
    (req : Request Principal Resource Value) : Prop :=
  E.member req.principal (E.tenantOf req.resource)

/-- A store assigns a value to every resource. -/
abbrev Store (Resource : Type v) (Value : Type w) := Resource → Value

variable [DecidableEq Resource]

/-- One step of the isolation engine: the write is applied only if the member
check succeeds; otherwise the store is unchanged. -/
noncomputable def step (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value) :
    Store Resource Value :=
  if Authorized E req then Function.update σ req.resource req.value else σ

/-- Executing a whole trace of requests. -/
noncomputable def exec (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) : List (Request Principal Resource Value) →
    Store Resource Value
  | [] => σ
  | req :: rest => exec E (step E σ req) rest

@[simp] theorem exec_nil (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) : exec E σ [] = σ := rfl

@[simp] theorem exec_cons (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value)
    (rest : List (Request Principal Resource Value)) :
    exec E σ (req :: rest) = exec E (step E σ req) rest := rfl

/-- **Soundness of the guard (one step).** If a single step changes the stored
value at some resource `r`, then the request was authorized, targeted `r`, and
hence its issuer is a member of the tenant owning `r`. -/
theorem step_change_imp_member (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value)
    (r : Resource) (h : step E σ req r ≠ σ r) :
    req.resource = r ∧ Authorized E req ∧ E.member req.principal (E.tenantOf r) := by
  unfold step at h
  by_cases hauth : Authorized E req
  · rw [if_pos hauth] at h
    by_cases hr : req.resource = r
    · subst hr
      exact ⟨rfl, hauth, hauth⟩
    · -- `Function.update_of_ne` : updating at a different point leaves the value alone
      exact absurd (Function.update_of_ne (Ne.symm hr) _ _) h
  · rw [if_neg hauth] at h
    exact absurd rfl h

/-- A step performed by a principal that is *not* a member of tenant `t` leaves
every resource of tenant `t` untouched. -/
theorem step_preserves_of_not_member (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value) (t : Tenant)
    (hnm : ¬ E.member req.principal t) (r : Resource) (hr : E.tenantOf r = t) :
    step E σ req r = σ r := by
  by_contra hne
  obtain ⟨-, -, hmem⟩ := step_change_imp_member E σ req r hne
  exact hnm (hr ▸ hmem)

/-- **Member check prevents cross-tenant writes.**

In the isolation engine, a trace of write requests all issued by principals that
are *not* members of tenant `t` cannot modify any resource owned by `t`: the
final store agrees with the initial store on every such resource.

(The one-step core is `step_change_imp_member`, which rests on Mathlib's
`Function.update_of_ne`.) -/
theorem member_check_prevents_cross_tenant_write
    (E : Env Tenant Principal Resource) (σ : Store Resource Value)
    (reqs : List (Request Principal Resource Value)) (t : Tenant)
    (hout : ∀ req ∈ reqs, ¬ E.member req.principal t)
    (r : Resource) (hr : E.tenantOf r = t) :
    exec E σ reqs r = σ r := by
  induction reqs generalizing σ with
  | nil => rfl
  | cons req rest ih =>
      rw [exec_cons]
      rw [ih (step E σ req) (fun q hq => hout q (List.mem_cons_of_mem _ hq))]
      exact step_preserves_of_not_member E σ req t
        (hout req (List.mem_cons_self ..)) r hr

/-- **Completeness of the guard.** An authorized write really does take effect:
if the issuing principal is a member of the tenant owning the target resource,
the value is stored. -/
theorem step_of_member (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (req : Request Principal Resource Value)
    (h : E.member req.principal (E.tenantOf req.resource)) :
    step E σ req req.resource = req.value := by
  rw [step, if_pos (show Authorized E req from h), Function.update_self]

/-- Contrapositive form: an *effective* write to a resource of tenant `t` can
only be issued by a member of `t`. -/
theorem writer_is_member (E : Env Tenant Principal Resource)
    (σ : Store Resource Value) (reqs : List (Request Principal Resource Value))
    (r : Resource) (h : exec E σ reqs r ≠ σ r) :
    ∃ req ∈ reqs, E.member req.principal (E.tenantOf r) := by
  by_contra hcon
  push_neg at hcon
  exact h (member_check_prevents_cross_tenant_write E σ reqs (E.tenantOf r)
    (fun req hreq => hcon req hreq) r rfl)

section Sanity

/-- A concrete two-tenant instance: resources and principals are booleans, and
principal `p` is a member of tenant `t` iff `p = t`. -/
def demoEnv : Env Bool Bool Bool where
  tenantOf := id
  member p t := p = t

/-- A cross-tenant write really is blocked in the concrete instance. -/
example (σ : Store Bool ℕ) :
    step demoEnv σ ⟨false, true, 7⟩ = σ := by
  have h : ¬ Authorized demoEnv (Value := ℕ) ⟨false, true, 7⟩ := by
    simp [Authorized, demoEnv]
  rw [step, if_neg h]

/-- An in-tenant write really goes through in the concrete instance. -/
example (σ : Store Bool ℕ) :
    step demoEnv σ ⟨true, true, 7⟩ true = 7 :=
  step_of_member demoEnv σ ⟨true, true, 7⟩ rfl

end Sanity

end WriteIntegrity
end PCA

