/-!
# Alter Policy Preserves Roles And Cmd
Category: Proof-Carrying Apps
Target: PCA.Fix.alter_policy_preserves_roles_and_cmd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Fix

/-- A role name granted to a principal by the isolation engine. -/
abbrev Role := String

/-- A command that a principal may attempt to run. -/
abbrev Cmd := String

/-- A policy of the isolation engine: which role may run which command. -/
structure Policy where
  grants : Role → Cmd → Bool

/-- A configuration of the isolation engine: the roles held by the current
principal, the command under consideration, the active policy, and an audit log. -/
structure Config where
  roles : List Role
  cmd : Cmd
  policy : Policy
  log : List String

/-- The command of a configuration is authorized when some held role grants it. -/
def Config.authorized (c : Config) : Bool :=
  c.roles.any (fun r => c.policy.grants r c.cmd)

/-- Altering the policy: the engine installs the new policy and appends a fresh
audit entry recording the new decision, leaving roles and command untouched. -/
def alterPolicy (f : Policy → Policy) (c : Config) : Config :=
  let p' := f c.policy
  { roles := c.roles
    cmd := c.cmd
    policy := p'
    log := (if c.roles.any (fun r => p'.grants r c.cmd) then "allow" else "deny") :: c.log }

/-- **Main result.** Altering the policy preserves both the roles held by the
principal and the command under consideration. -/
theorem alter_policy_preserves_roles_and_cmd (f : Policy → Policy) (c : Config) :
    (alterPolicy f c).roles = c.roles ∧ (alterPolicy f c).cmd = c.cmd :=
  ⟨rfl, rfl⟩

/-- The altered configuration carries exactly the new policy. -/
theorem alter_policy_policy (f : Policy → Policy) (c : Config) :
    (alterPolicy f c).policy = f c.policy := rfl

/-- The authorization decision after an alteration is the decision of the new
policy on the (unchanged) roles and command. -/
theorem authorized_alterPolicy (f : Policy → Policy) (c : Config) :
    (alterPolicy f c).authorized = c.roles.any (fun r => (f c.policy).grants r c.cmd) := rfl

/-- Altering by the identity leaves roles, command and policy unchanged
(only the audit log grows). -/
theorem alter_policy_id (c : Config) :
    (alterPolicy id c).roles = c.roles ∧ (alterPolicy id c).cmd = c.cmd ∧
      (alterPolicy id c).policy = c.policy :=
  ⟨rfl, rfl, rfl⟩

/-- Successive alterations still preserve roles and command, and compose on policies. -/
theorem alter_policy_comp (f g : Policy → Policy) (c : Config) :
    (alterPolicy g (alterPolicy f c)).roles = c.roles ∧
      (alterPolicy g (alterPolicy f c)).cmd = c.cmd ∧
      (alterPolicy g (alterPolicy f c)).policy = g (f c.policy) :=
  ⟨rfl, rfl, rfl⟩

/-- The audit log only ever grows under an alteration: the previous log is a suffix. -/
theorem alter_policy_log_suffix (f : Policy → Policy) (c : Config) :
    c.log <:+ (alterPolicy f c).log :=
  ⟨[(if c.roles.any (fun r => (f c.policy).grants r c.cmd) then "allow" else "deny")], rfl⟩

end PCA.Fix

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

