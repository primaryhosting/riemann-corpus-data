/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which must be the very
-- first command in the file; Lean therefore forbids any `import` after it. The development
-- below is consequently written against the Lean 4 core library only (no Mathlib lemmas are
-- needed: the goals are closed by `rfl`, `simp` and `omega`, all available in core).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: it targets a memory `region`,
carries a `payload`, and presents a capability certificate `cert` that is supposed to
witness the writer's authority over that region. -/
structure Write where
  region : Nat
  payload : Nat
  cert : Nat
  deriving DecidableEq

/-- `key r` is the capability token authorizing writes to region `r`.
A write is *authentic* exactly when the certificate it presents is the region's token. -/
def Authentic (key : Nat → Nat) (w : Write) : Prop := w.cert = key w.region

instance (key : Nat → Nat) (w : Write) : Decidable (Authentic key w) := by
  unfold Authentic; infer_instance

/-- The engine's admission relation: a write is let through exactly when the runtime
`check` accepts it. -/
def Admits (check : Write → Bool) (w : Write) : Prop := check w = true

/-- Write integrity (soundness of the engine's `check`): every admitted write is authentic. -/
def Sound (key : Nat → Nat) (check : Write → Bool) : Prop :=
  ∀ w : Write, Admits check w → Authentic key w

/-- A *forgery* against a checker: a write that the engine admits although it is not
authentic. -/
def Forges (key : Nat → Nat) (check : Write → Bool) (w : Write) : Prop :=
  Admits check w ∧ ¬ Authentic key w

/-- **With a trivially-true check, the engine admits a forgery.**

If the isolation engine's write check is the constant `true` predicate, then for *any*
capability assignment `key` there is a write that is admitted yet carries a bogus
certificate; consequently the engine's write-integrity property `Sound` fails.

Interpretation: an always-accepting check discharges no proof obligation, so the
proof-carrying discipline degenerates and write integrity is lost. -/
theorem with_check_true_admits_forge (key : Nat → Nat) :
    (∃ w : Write, Forges key (fun _ => true) w) ∧ ¬ Sound key (fun _ => true) := by
  have hforge : Forges key (fun _ => true) ⟨0, 0, key 0 + 1⟩ := by
    refine ⟨rfl, ?_⟩
    intro h
    simp only [Authentic] at h
    omega
  refine ⟨⟨_, hforge⟩, ?_⟩
  intro hs
  exact hforge.2 (hs _ hforge.1)

end PCA.WriteIntegrity

#print axioms PCA.WriteIntegrity.with_check_true_admits_forge

