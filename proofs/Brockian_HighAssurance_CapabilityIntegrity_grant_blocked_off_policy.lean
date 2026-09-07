import Mathlib

/-!
# seL4-class Integrity: Authority Confinement for a Capability System

An AXLE-verified Lean 4 demonstrator of the *integrity* property at the heart of
seL4's security proof, specialised to a capability-based access-control model.

The property proved — **authority confinement** — states that a system whose
initial capabilities lie within an authorising security policy can never, through
any finite sequence of guarded operations, manufacture authority the policy does
not permit. This is the access-control analogue of seL4's integrity theorem
(the kernel never writes/grants beyond the authority the policy grants a subject).

The proof is *general*: it is an induction over the reflexive–transitive closure
of the transition relation, i.e. over arbitrary operation sequences of any length,
not a `decide` enumeration of a fixed configuration.
-/

namespace Brockian.HighAssurance.CapabilityIntegrity

/-- Access rights a capability may confer (seL4-flavoured: read / write / grant). -/
inductive Right where
  | read
  | write
  | grant
  deriving DecidableEq

/-- A capability names a `(subject, object, right)` triple: subject `s` holds
`right` on `object`. Subjects and objects are natural numbers (identifiers). -/
abbrev Cap : Type := ℕ × ℕ × Right

/-- The system **state** is the finite set of capabilities currently held. -/
abbrev State : Type := Finset Cap

/-- The security **policy**: the finite set of *authorised* capabilities. The
integrity property is stated relative to this policy. -/
abbrev Policy : Type := Finset Cap

/-- The guarded transition relation. Two operations are modelled:

* `grant`: subject `a` grants `right r` on object `o` to subject `b`.  This fires
  **only if** (i) `a` currently holds a `grant` capability on `o`
  (`(a, o, Right.grant) ∈ s`) *and* actually holds the right it is delegating
  (`(a, o, r) ∈ s`), **and** (ii) the newly created capability `(b, o, r)` is
  authorised by the policy (`(b, o, r) ∈ P`).  Guard (ii) is what enforces
  integrity: no operation may mint a capability outside the policy.

* `revoke`: any held capability may be dropped.  Removing authority is always
  integrity-safe, so this operation is unconditional. -/
inductive step (P : Policy) : State → State → Prop where
  | grant (a b o : ℕ) (r : Right) (s : State)
      (hgrant : (a, o, Right.grant) ∈ s)
      (hhold  : (a, o, r) ∈ s)
      (hpol   : (b, o, r) ∈ P) :
      step P s (insert (b, o, r) s)
  | revoke (c : Cap) (s : State) :
      step P s (s.erase c)

/-- `Reachable P s0 s` : state `s` is reachable from `s0` by finitely many guarded
operations — the reflexive–transitive closure of `step P`. -/
def Reachable (P : Policy) : State → State → Prop :=
  Relation.ReflTransGen (step P)

/-- **Core invariant lemma.** Any capability that a single guarded step *adds* to
the state is authorised by the policy. The `grant` guard (ii) supplies exactly
this; `revoke` adds nothing. -/
theorem step_added_in_policy (P : Policy) {s s' : State} (h : step P s s')
    {c : Cap} (hc : c ∈ s') (hnew : c ∉ s) : c ∈ P := by
  cases h with
  | grant a b o r s hgrant hhold hpol =>
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hpol
      · exact absurd hc hnew
  | revoke c0 s =>
      exact absurd (Finset.mem_of_mem_erase hc) hnew

/-- **Single-step integrity preservation.** If every held capability is within the
policy, it remains so after any one guarded operation. -/
theorem step_preserves (P : Policy) {s s' : State} (hs : s ⊆ P)
    (h : step P s s') : s' ⊆ P := by
  intro x hx
  by_cases hmem : x ∈ s
  · exact hs hmem
  · exact step_added_in_policy P h hx hmem

/-- **Integrity — authority confinement (the seL4 integrity analogue).**
If the initial capabilities are within the policy (`s0 ⊆ P`), then *every*
reachable state's capabilities remain within the policy. The system can never
create authority the policy does not permit, over arbitrarily long operation
sequences. Proved by induction on the reachability (reflexive–transitive closure)
relation: the base case is the hypothesis, and each step preserves `⊆ P` because
the `grant` guard forces any newly minted capability into `P`. -/
theorem integrity_confinement (P : Policy) (s0 s : State)
    (hsub : s0 ⊆ P) (hreach : Reachable P s0 s) : s ⊆ P := by
  induction hreach with
  | refl => exact hsub
  | tail _ hstep ih => exact step_preserves P ih hstep

/-! ## Non-vacuity: the model has real dynamics and the guard really blocks -/

/-- **Non-vacuity (progress).** Authority genuinely flows when the policy permits
it: there is a concrete policy, start state, and successor with `step P s0 s` and
`s ≠ s0`. Here subject `1` holds a grant-capability and the read right on object
`5`, and the policy authorises granting read on `5` to subject `2`; the grant
fires and produces a strictly larger state. -/
theorem grant_can_progress :
    ∃ (P s0 s : State), step P s0 s ∧ s ≠ s0 := by
  refine ⟨{(2, 5, Right.read)},
          {(1, 5, Right.grant), (1, 5, Right.read)},
          insert (2, 5, Right.read) {(1, 5, Right.grant), (1, 5, Right.read)},
          ?_, ?_⟩
  · exact step.grant 1 2 5 Right.read {(1, 5, Right.grant), (1, 5, Right.read)}
      (by decide) (by decide) (by decide)
  · decide

/-- **Non-vacuity (the guard blocks).** With a policy that does *not* authorise
`(2, 5, Right.write)`, no single step starting from the same state can introduce
that capability. This is the operational witness that guard (ii) actually rejects
unauthorised authority (delete guard (ii) and this becomes false). -/
theorem grant_blocked_off_policy :
    ¬ ∃ s, step ({(2, 5, Right.read)} : State)
              {(1, 5, Right.grant), (1, 5, Right.read)} s
            ∧ (2, 5, Right.write) ∈ s
            ∧ (2, 5, Right.write) ∉ ({(1, 5, Right.grant), (1, 5, Right.read)} : State) := by
  rintro ⟨s, hstep, hmem, hnot⟩
  have hin : (2, 5, Right.write) ∈ ({(2, 5, Right.read)} : State) :=
    step_added_in_policy _ hstep hmem hnot
  exact absurd hin (by decide)

/-- **Non-vacuity (the theorem excludes real bad states).** The state
`{(2, 5, Right.write)}` is *not* within the policy `{(2, 5, Right.read)}`, and it is
provably *not reachable* from the in-policy start state `∅`. Hence
`integrity_confinement` is not vacuously true — it genuinely rules out reaching
states that hold unauthorised authority. -/
theorem integrity_is_nontrivial :
    ∃ (P s0 t : State), s0 ⊆ P ∧ ¬ t ⊆ P ∧ ¬ Reachable P s0 t := by
  refine ⟨{(2, 5, Right.read)}, ∅, {(2, 5, Right.write)},
          Finset.empty_subset _, by decide, ?_⟩
  intro hreach
  have hsub : ({(2, 5, Right.write)} : State) ⊆ {(2, 5, Right.read)} :=
    integrity_confinement _ _ _ (Finset.empty_subset _) hreach
  exact absurd hsub (by decide)

end Brockian.HighAssurance.CapabilityIntegrity
