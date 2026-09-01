/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

namespace PCA
namespace WriteIntegrity

/-- A write request submitted to the isolation engine: a principal asks to store
`value` at `key`, presenting the authorization `token` that is supposed to witness
that the write is permitted. -/
structure Write where
  /-- The principal issuing the write. -/
  principal : Nat
  /-- The location being written. -/
  key : Nat
  /-- The value being written. -/
  value : Nat
  /-- The authorization token presented with the request. -/
  token : Nat
  deriving DecidableEq, Repr

/-- The write policy of the isolation engine: which principals may write which
keys, together with the unique token that authorizes each such write. -/
structure Policy where
  /-- `mayWrite p k` holds when principal `p` is permitted to write key `k`. -/
  mayWrite : Nat → Nat → Prop
  /-- `token p k` is the one token that authorizes `p` to write `k`. -/
  token : Nat → Nat → Nat

/-- A write is *authorized* by the policy when the principal is permitted to write
the key **and** presents the matching token. -/
def Authorized (P : Policy) (w : Write) : Prop :=
  P.mayWrite w.principal w.key ∧ w.token = P.token w.principal w.key

/-- The engine's admission check: a predicate on write requests. -/
abbrev Check := Write → Bool

/-- The engine accepts a write exactly when its check succeeds. -/
def Accepts (check : Check) (w : Write) : Prop :=
  check w = true

/-- The degenerate check that accepts every request. -/
def trueCheck : Check := fun _ => true

/-- Write-integrity soundness: every accepted write is authorized by the policy. -/
def Sound (P : Policy) (check : Check) : Prop :=
  ∀ w : Write, Accepts check w → Authorized P w

/-- A *forgery*: a write the engine accepts even though the policy does not
authorize it. -/
def Forge (P : Policy) (check : Check) (w : Write) : Prop :=
  Accepts check w ∧ ¬ Authorized P w

/-- The forged request used below: it presents a token that cannot be the
policy's token for principal `0` and key `0`. -/
def forgedWrite (P : Policy) : Write :=
  { principal := 0, key := 0, value := 0, token := P.token 0 0 + 1 }

/-- The exhibited request is never authorized: its token differs from the
policy's token for that principal and key. -/
theorem forgedWrite_not_authorized (P : Policy) : ¬ Authorized P (forgedWrite P) := by
  rintro ⟨-, htok⟩
  simp only [forgedWrite] at htok
  omega

/-- Any engine whose admission check is identically `true` admits a forgery:
for every policy there is a write request the engine accepts but the policy does
not authorize, hence such an engine is not write-integrity sound. -/
theorem with_check_true_admits_forge (P : Policy) :
    Forge P trueCheck (forgedWrite P) ∧ ¬ Sound P trueCheck := by
  have hforge : Forge P trueCheck (forgedWrite P) :=
    ⟨rfl, forgedWrite_not_authorized P⟩
  exact ⟨hforge, fun hsound => hforge.2 (hsound (forgedWrite P) hforge.1)⟩

end WriteIntegrity
end PCA

