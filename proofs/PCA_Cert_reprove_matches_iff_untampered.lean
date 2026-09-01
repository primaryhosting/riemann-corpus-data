/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which Lean treats
-- as a command; consequently no `import` line may follow it.  The development below
-- is therefore self-contained and uses only the Lean 4 core library.

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

/-- An artifact shipped by the isolation engine: a code image together with the
policy/configuration it is meant to run under. -/
structure Artifact where
  /-- The code image, as a byte (word) list. -/
  code : List Nat
  /-- The policy/configuration image, as a byte (word) list. -/
  policy : List Nat
deriving DecidableEq

/-- A length-prefixed serialization of an artifact.  The length prefix makes the
encoding unambiguous, i.e. injective. -/
def Artifact.encode (a : Artifact) : List Nat :=
  a.code.length :: (a.code ++ a.policy)

theorem Artifact.encode_injective : Function.Injective Artifact.encode := by
  rintro ⟨c₁, p₁⟩ ⟨c₂, p₂⟩ h
  simp only [Artifact.encode, List.cons.injEq] at h
  obtain ⟨hlen, happ⟩ := h
  obtain ⟨hc, hp⟩ := List.append_inj happ hlen
  simp [hc, hp]

/-- A certificate accompanying an artifact: the digest of the artifact together
with the identifier of the safety claim that was discharged for it. -/
structure Cert where
  /-- Digest of the (serialized) artifact. -/
  digest : Nat
  /-- Identifier of the safety claim established for the artifact. -/
  claim : Nat
deriving DecidableEq

namespace Cert

variable (hash : List Nat → Nat) (claimOf : Artifact → Nat)

/-- Certification: run the checker on the artifact, recording its digest and the
claim that was established. -/
def certify (a : Artifact) : Cert :=
  ⟨hash a.encode, claimOf a⟩

/-- Re-proving is just re-running certification on the artifact at hand; the
checker is deterministic. -/
def reprove (a : Artifact) : Cert :=
  certify hash claimOf a

theorem reprove_eq_certify (a : Artifact) :
    reprove hash claimOf a = certify hash claimOf a := rfl

/-- **Soundness and completeness of the isolation engine's tamper check.**

Given a collision-free digest function `hash`, a certificate `c` issued for the
original artifact `orig`, and a received artifact `recv`, re-proving `recv`
reproduces the certificate `c` exactly when `recv` has not been tampered with,
i.e. when `recv = orig`.

Left-to-right is soundness of the check: a matching re-proof witnesses integrity.
Right-to-left is completeness: an untampered artifact always re-certifies to the
same certificate, since the checker is deterministic. -/
theorem reprove_matches_iff_untampered
    (hinj : Function.Injective hash)
    (orig recv : Artifact) (c : Cert) (hc : c = certify hash claimOf orig) :
    reprove hash claimOf recv = c ↔ recv = orig := by
  subst hc
  constructor
  · intro h
    have hd : hash recv.encode = hash orig.encode := congrArg Cert.digest h
    exact Artifact.encode_injective (hinj hd)
  · rintro rfl
    rfl

/-- Contrapositive reading: any tampering with the artifact is detected by
re-proving. -/
theorem reprove_ne_of_tampered
    (hinj : Function.Injective hash)
    (orig recv : Artifact) (c : Cert) (hc : c = certify hash claimOf orig)
    (htamper : recv ≠ orig) :
    reprove hash claimOf recv ≠ c := by
  intro h
  exact htamper ((reprove_matches_iff_untampered hash claimOf hinj orig recv c hc).mp h)

end Cert

end PCA

#print axioms PCA.Cert.reprove_matches_iff_untampered

