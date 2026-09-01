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
# Member Check Prevents Cross Tenant Write
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.member_check_prevents_cross_tenant_write
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

universe u v w x

/-- A tenancy policy for the isolation engine: every resource belongs to exactly
one tenant, and each principal is a member of some collection of tenants. -/
structure Policy (Principal : Type u) (Resource : Type v) (Tenant : Type w) where
  /-- The (unique) tenant owning a given resource. -/
  tenantOf : Resource → Tenant
  /-- Membership relation between principals and tenants. -/
  member : Principal → Tenant → Prop

/-- A write request: a principal asking to store `value` at `target`. -/
structure Write (Principal : Type u) (Resource : Type v) (Value : Type x) where
  /-- The principal issuing the write. -/
  actor : Principal
  /-- The resource being written. -/
  target : Resource
  /-- The value to be written. -/
  value : Value

variable {Principal : Type u} {Resource : Type v} {Tenant : Type w} {Value : Type x}

/-- Point update of a store, i.e. `Function.update` specialised to the
non-dependent stores used here (kept local so that this module is
dependency-free; it agrees with `Function.update` from Mathlib). -/
noncomputable def update (st : Resource → Value) (a : Resource) (v : Value) :
    Resource → Value :=
  open Classical in
  fun r => if r = a then v else st r

@[simp]
theorem update_self (st : Resource → Value) (a : Resource) (v : Value) :
    update st a v a = v := by
  classical
  simp [update]

/-- The analogue of Mathlib's `Function.update_of_ne`. -/
theorem update_of_ne {st : Resource → Value} {a r : Resource} (h : r ≠ a) (v : Value) :
    update st a v r = st r := by
  classical
  simp [update, h]

/-- The isolation engine's guard: a write is authorized exactly when the actor is
a member of the tenant owning the targeted resource. -/
def Authorized (P : Policy Principal Resource Tenant)
    (w : Write Principal Resource Value) : Prop :=
  P.member w.actor (P.tenantOf w.target)

/-- The state transition performed by the engine on a write request: the store is
updated at the target if and only if the member check succeeds; otherwise the
write is dropped. -/
noncomputable def applyWrite (P : Policy Principal Resource Tenant)
    (st : Resource → Value) (w : Write Principal Resource Value) : Resource → Value :=
  open Classical in
  if Authorized P w then update st w.target w.value else st

/-- **Soundness of the member check (no cross-tenant writes).**
No resource belonging to a tenant of which the actor is *not* a member can be
modified by the engine: such a request is either rejected by the member check, or
it targets a resource in a tenant the actor does belong to, hence a *different*
resource, and point updates leave other points fixed. -/
theorem member_check_prevents_cross_tenant_write
    (P : Policy Principal Resource Tenant) (st : Resource → Value)
    (w : Write Principal Resource Value) (r : Resource)
    (hr : ¬ P.member w.actor (P.tenantOf r)) :
    applyWrite P st w r = st r := by
  classical
  unfold applyWrite
  by_cases h : Authorized P w
  · have hne : r ≠ w.target := by
      intro hEq
      subst hEq
      exact hr h
    rw [if_pos h]
    exact update_of_ne hne _
  · rw [if_neg h]

/-- **Completeness of the member check.** A same-tenant (hence authorized) write
does take effect at its target. -/
theorem member_check_allows_same_tenant_write
    (P : Policy Principal Resource Tenant) (st : Resource → Value)
    (w : Write Principal Resource Value)
    (hw : P.member w.actor (P.tenantOf w.target)) :
    applyWrite P st w w.target = w.value := by
  classical
  have hA : Authorized P w := hw
  unfold applyWrite
  rw [if_pos hA]
  exact update_self _ _ _

/-- Tenant-level isolation: the store restricted to any tenant `t` of which the
actor is not a member is left completely unchanged. -/
theorem applyWrite_eq_on_foreign_tenant
    (P : Policy Principal Resource Tenant) (st : Resource → Value)
    (w : Write Principal Resource Value) (t : Tenant)
    (ht : ¬ P.member w.actor t) (r : Resource) (hr : P.tenantOf r = t) :
    applyWrite P st w r = st r := by
  refine member_check_prevents_cross_tenant_write P st w r ?_
  rw [hr]
  exact ht

end WriteIntegrity
end PCA

