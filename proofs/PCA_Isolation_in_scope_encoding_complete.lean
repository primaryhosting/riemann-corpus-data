/-
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# In Scope Encoding Complete
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_complete
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace PCA.Isolation

/-- A request made by a sandboxed app: a resource together with a write flag
(`write = false` means read-only access). -/
structure Request (R : Type*) where
  resource : R
  write : Bool
  deriving DecidableEq

/-- A *scope* granted to a sandboxed app is the set of resources it may touch. -/
abbrev Scope (R : Type*) := Set R

variable {R : Type*}

/-- A request is *in scope* when the resource it names belongs to the granted scope. -/
def InScope (s : Scope R) (req : Request R) : Prop := req.resource ∈ s

variable [Encodable R]

/-- The isolation engine's wire encoding of a request: the code of its resource
paired with its write bit. -/
def encodeRequest (req : Request R) : ℕ :=
  Nat.pair (Encodable.encode req.resource) (cond req.write 1 0)

/-- The isolation engine's decoder, *relative to a granted scope*: a code is
accepted only if it names a decodable resource lying inside the scope. -/
def decodeRequest (s : Scope R) [DecidablePred (· ∈ s)] (n : ℕ) : Option (Request R) :=
  (Encodable.decode (α := R) (Nat.unpair n).1).bind fun r =>
    if r ∈ s then some ⟨r, decide ((Nat.unpair n).2 = 1)⟩ else none

/-- **Completeness of the in-scope encoding.** Every request that lies inside the
granted scope survives the engine's encode/decode round trip: no in-scope request
is ever rejected or altered by the isolation boundary.

The key ingredient is Mathlib's `Encodable.encodek` (`decode (encode a) = some a`),
together with `Nat.unpair_pair`. -/
theorem in_scope_encoding_complete (s : Scope R) [DecidablePred (· ∈ s)]
    (req : Request R) (h : InScope s req) :
    decodeRequest s (encodeRequest req) = some req := by
  obtain ⟨r, w⟩ := req
  simp only [InScope] at h
  simp only [decodeRequest, encodeRequest, Nat.unpair_pair, Encodable.encodek,
    Option.bind_some, if_pos h, Option.some.injEq, Request.mk.injEq, true_and]
  cases w <;> simp

/-- **Soundness of the in-scope decoder.** Anything the decoder accepts is a
request that lies inside the granted scope. -/
theorem decode_in_scope (s : Scope R) [DecidablePred (· ∈ s)] {n : ℕ} {req : Request R}
    (h : decodeRequest s n = some req) : InScope s req := by
  simp only [decodeRequest, Option.bind_eq_some_iff] at h
  obtain ⟨r, -, hr⟩ := h
  by_cases hs : r ∈ s
  · simp only [if_pos hs, Option.some.injEq] at hr
    subst hr
    exact hs
  · simp [hs] at hr

/-- The decoder's accepted requests are exactly the in-scope requests: the
isolation model is both sound and complete. -/
theorem range_decodeRequest (s : Scope R) [DecidablePred (· ∈ s)] (req : Request R) :
    (∃ n : ℕ, decodeRequest s n = some req) ↔ InScope s req :=
  ⟨fun ⟨_, hn⟩ => decode_in_scope s hn, fun h => ⟨encodeRequest req,
    in_scope_encoding_complete s req h⟩⟩

end PCA.Isolation

