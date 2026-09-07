/-!
# Proof-Carrying Apps — Fix / repair actions (`PCA.Fix` namespace)

Category: Proof-Carrying Apps
Provenance: Aristotle theorem prover (Harmonic); assembled from the AXLE-verified
best-proof file into one registered module.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-- A role held by a principal in the isolation engine's model. -/
abbrev Role := String

/-- A command that a proof-carrying app may attempt to run. -/
abbrev Cmd := String

/-- A policy of the isolation engine: which `(cmd, role)` pairs are permitted. -/
structure Policy where
  /-- `allowed c r` says the policy lets role `r` execute command `c`. -/
  allowed : Cmd → Role → Bool

/-- A capability request handled by the isolation engine: a command, the roles
carried by the requesting principal, and the policy in force. -/
structure Capability where
  /-- The command being requested. -/
  cmd : Cmd
  /-- The roles carried by the requesting principal. -/
  roles : List Role
  /-- The policy currently in force. -/
  policy : Policy

/-- The engine's decision procedure: the request is granted iff some carried
role is permitted to run the command by the policy in force. -/
def Capability.granted (c : Capability) : Bool :=
  c.roles.any fun r => c.policy.allowed c.cmd r

namespace Fix

/-- The "alter policy" repair action of the isolation engine: swap in a new
policy, leaving the request's command and roles untouched. -/
def alterPolicy (c : Capability) (p : Policy) : Capability :=
  { c with policy := p }

/-- **Target.** Altering the policy in force preserves both the roles carried by
the request and the command being requested, while installing exactly the
supplied policy. -/
theorem alter_policy_preserves_roles_and_cmd (c : Capability) (p : Policy) :
    (alterPolicy c p).roles = c.roles ∧
      (alterPolicy c p).cmd = c.cmd ∧
      (alterPolicy c p).policy = p :=
  ⟨rfl, rfl, rfl⟩

/-- Consequence for the engine's decision procedure: after altering the policy,
the grant decision is obtained by evaluating the *new* policy against the
*unchanged* command and roles. -/
theorem granted_alterPolicy (c : Capability) (p : Policy) :
    (alterPolicy c p).granted = c.roles.any fun r => p.allowed c.cmd r := by
  obtain ⟨hroles, hcmd, hpolicy⟩ := alter_policy_preserves_roles_and_cmd c p
  simp only [Capability.granted, hroles, hcmd, hpolicy]

/-- Altering the policy twice is the same as altering it once with the second
policy. -/
theorem alterPolicy_alterPolicy (c : Capability) (p q : Policy) :
    alterPolicy (alterPolicy c p) q = alterPolicy c q := rfl

/-- Re-installing the policy already in force is a no-op. -/
theorem alterPolicy_self (c : Capability) : alterPolicy c c.policy = c := rfl

end Fix

end PCA
