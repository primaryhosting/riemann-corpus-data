import Mathlib

/-!
# A Unified Capability-Microkernel State Machine with One Composite Security Invariant

This module gives a compact but faithful model of a high-assurance capability
microkernel and proves, once and for all, that a single COMPOSITE security policy
is preserved across *every* reachable state.

The composite invariant folds together three classical security dimensions:

* **Integrity** — every capability held in the kernel lies within the static
  authority (`capAuth`);
* **Memory separation** — every memory address whose owning writer is recorded was
  written by a subject authorized to write it (`writeAuth`);
* **IPC confinement** — every delivered message sits in the mailbox of a subject
  authorized to receive on the endpoint it came in on, and was sent by a subject
  authorized to send on that endpoint (`sendAuth`/`recvAuth`).

The headline theorem `kernel_security` states: from any policy-conformant initial
state, *every* reachable kernel state satisfies the whole composite policy.  This is
the "the entire kernel model preserves its security policy across arbitrary
execution" result.
-/

namespace Brockian.HighAssurance.Kernel

/-! ## Basic sorts (all modeled as `ℕ`) -/

abbrev Subject  := ℕ
abbrev Object   := ℕ
abbrev Addr     := ℕ
abbrev Endpoint := ℕ
abbrev Msg      := ℕ

/-- A delivered IPC message, tagged with its sender and the endpoint it arrived on,
    so that confinement can be checked on the received copy. -/
structure Delivered where
  sender   : Subject
  endpoint : Endpoint
  payload  : Msg
  deriving DecidableEq

/-! ## Static policy: the four authorities -/

/-- The static security policy: it fixes, once and for all, which subjects may hold
    which capabilities, write which addresses, and send/receive on which endpoints.
    All four relations are decidable so that concrete non-vacuity witnesses reduce by
    `decide`. -/
structure Policy where
  writeAuth : Subject → Addr → Prop
  capAuth   : Subject → Object → Prop
  sendAuth  : Subject → Endpoint → Prop
  recvAuth  : Subject → Endpoint → Prop
  writeAuth_dec : ∀ s a, Decidable (writeAuth s a)
  capAuth_dec   : ∀ s o, Decidable (capAuth s o)
  sendAuth_dec  : ∀ s e, Decidable (sendAuth s e)
  recvAuth_dec  : ∀ s e, Decidable (recvAuth s e)

attribute [instance] Policy.writeAuth_dec Policy.capAuth_dec
attribute [instance] Policy.sendAuth_dec Policy.recvAuth_dec

/-! ## Kernel state -/

/-- The mutable kernel state.

* `caps`      — the capability table: `(s, o) ∈ caps` means subject `s` holds a
  capability naming object `o`;
* `mem`       — the contents of memory;
* `writer`    — provenance: `writer a = some s` records that `s` performed the last
  authorized write to address `a` (`none` = never written);
* `mailbox`   — per-subject inbox of delivered messages. -/
structure KernelState where
  caps    : Finset (Subject × Object)
  mem     : Addr → ℕ
  writer  : Addr → Option Subject
  mailbox : Subject → List Delivered

/-! ## The guarded step relation -/

/-- Kernel operations, each carrying its arguments. -/
inductive KOp where
  | grantCap (a b : Subject) (o : Object)
  | writeMem (s : Subject) (addr : Addr) (v : ℕ)
  | sendMsg  (frm : Subject) (ep : Endpoint) (dst : Subject) (m : Msg)

/-- The single-step transition relation of the kernel.  Each constructor is a
    reference-monitor rule: it fires only when the operation is permitted by the
    static policy, and it updates exactly the state fragment it is allowed to touch.

* `grantCap` inserts a capability `(b, o)` only when `capAuth b o` holds, so no
  out-of-policy capability can ever enter the table;
* `writeMem` updates `mem addr` and records `writer addr := some s` only when
  `writeAuth s addr` holds;
* `sendMsg` delivers a message to `dst`'s mailbox only when both `sendAuth frm ep`
  and `recvAuth dst ep` hold. -/
inductive kstep (P : Policy) : KernelState → KernelState → Prop where
  | grantCap {st : KernelState} (a b : Subject) (o : Object)
      (hcap : P.capAuth b o) :
      kstep P st { st with caps := insert (b, o) st.caps }
  | writeMem {st : KernelState} (s : Subject) (addr : Addr) (v : ℕ)
      (hw : P.writeAuth s addr) :
      kstep P st
        { st with
          mem    := Function.update st.mem addr v
          writer := Function.update st.writer addr (some s) }
  | sendMsg {st : KernelState} (frm : Subject) (ep : Endpoint) (dst : Subject) (m : Msg)
      (hs : P.sendAuth frm ep) (hr : P.recvAuth dst ep) :
      kstep P st
        { st with
          mailbox :=
            Function.update st.mailbox dst
              (⟨frm, ep, m⟩ :: st.mailbox dst) }

/-- Reachability: reflexive–transitive closure of the guarded step relation. -/
def Reachable (P : Policy) : KernelState → KernelState → Prop :=
  Relation.ReflTransGen (kstep P)

/-! ## The composite security invariant -/

/-- The **composite kernel security policy**.  A state is secure exactly when all
    three security dimensions hold simultaneously:

1. **integrity** — every held capability is within capability-authority;
2. **separation** — every recorded memory write was authorized;
3. **confinement** — every delivered message is in an authorized receiver's mailbox
   and came from an authorized sender on its endpoint. -/
def KernelSecure (P : Policy) (st : KernelState) : Prop :=
  (∀ c ∈ st.caps, P.capAuth c.1 c.2)
  ∧ (∀ addr s, st.writer addr = some s → P.writeAuth s addr)
  ∧ (∀ dst d, d ∈ st.mailbox dst → P.recvAuth dst d.endpoint ∧ P.sendAuth d.sender d.endpoint)

/-! ## Preservation and the headline theorem -/

/-- **One-step preservation.**  A single guarded kernel step preserves the whole
    composite security policy.  Proved by cases on the operation: each guard forces
    exactly the conjunct that the operation could otherwise threaten, while the other
    two conjuncts are untouched. -/
theorem kstep_preserves (P : Policy) {s s' : KernelState}
    (hstep : kstep P s s') (hinv : KernelSecure P s) : KernelSecure P s' := by
  obtain ⟨hcaps, hwrite, hmail⟩ := hinv
  cases hstep with
  | grantCap a b o hcap =>
      refine ⟨?_, hwrite, hmail⟩
      intro c hc
      rw [Finset.mem_insert] at hc
      rcases hc with hc | hc
      · subst hc; simpa using hcap
      · exact hcaps c hc
  | writeMem sbj addr v hw =>
      refine ⟨hcaps, ?_, hmail⟩
      intro a s' hs'
      dsimp only at hs'
      by_cases ha : a = addr
      · subst ha
        rw [Function.update_self] at hs'
        injection hs' with e; subst e; exact hw
      · rw [Function.update_of_ne ha] at hs'
        exact hwrite a s' hs'
  | sendMsg frm ep dst m hs hr =>
      refine ⟨hcaps, hwrite, ?_⟩
      intro d dd hd
      dsimp only at hd
      by_cases hdst : d = dst
      · subst hdst
        rw [Function.update_self] at hd
        rw [List.mem_cons] at hd
        rcases hd with hd | hd
        · subst hd; exact ⟨hr, hs⟩
        · exact hmail d dd hd
      · rw [Function.update_of_ne hdst] at hd
        exact hmail d dd hd

/-- **The capstone.**  From any policy-conformant initial state, *every* reachable
    kernel state satisfies the whole composite security policy.  Proved by
    reflexive–transitive-closure induction, applying `kstep_preserves` at each step. -/
theorem kernel_security (P : Policy) (s0 s : KernelState)
    (h0 : KernelSecure P s0) (hreach : Reachable P s0 s) : KernelSecure P s := by
  induction hreach with
  | refl => exact h0
  | tail _ hstep ih => exact kstep_preserves P hstep ih

/-! ## Clean consequence: cross-subject memory isolation at the kernel level -/

/-- **Cross-subject memory isolation.**  In any reachable state (from a secure
    start), if the kernel records that subject `s'` wrote address `addr`, then `s'`
    was authorized to write `addr`.  No subject's write ever lands in another
    subject's address space without authority. -/
theorem reachable_writes_authorized (P : Policy) (s0 s : KernelState)
    (h0 : KernelSecure P s0) (hreach : Reachable P s0 s)
    (addr : Addr) (s' : Subject) (h : s.writer addr = some s') :
    P.writeAuth s' addr :=
  (kernel_security P s0 s h0 hreach).2.1 addr s' h

/-! ## Non-vacuity: a concrete policy, concrete runs, and an unreachable off-policy state -/

/-- A concrete decidable policy for the witnesses:

* subject `0` may write only even addresses; every subject may write address `0`;
* capability `(s, o)` is authorized iff `s ≤ o` (so `(5, 3)` is a *forbidden* cap);
* subject `s` may send/receive on endpoint `e` iff `s ≤ e`. -/
def demoPolicy : Policy where
  writeAuth s a := s = 0 → a % 2 = 0
  capAuth   s o := s ≤ o
  sendAuth  s e := s ≤ e
  recvAuth  s e := s ≤ e
  writeAuth_dec s a := inferInstanceAs (Decidable (s = 0 → a % 2 = 0))
  capAuth_dec   s o := inferInstanceAs (Decidable (s ≤ o))
  sendAuth_dec  s e := inferInstanceAs (Decidable (s ≤ e))
  recvAuth_dec  s e := inferInstanceAs (Decidable (s ≤ e))

/-- A concrete initial state: empty caps, zeroed memory, no writers, empty mailboxes. -/
def initState : KernelState where
  caps    := ∅
  mem     := fun _ => 0
  writer  := fun _ => none
  mailbox := fun _ => []

/-- The initial state is secure (vacuously on all three conjuncts). -/
theorem initState_secure : KernelSecure demoPolicy initState := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc; simp [initState] at hc
  · intro addr s h; simp [initState] at h
  · intro dst d h; simp [initState] at h

/-! ### (a) Authorized operations progress the state and preserve security. -/

/-- An authorized capability grant: subject `2` holds `(3, 7)` — authorized since
    `3 ≤ 7`.  The step fires. -/
theorem demo_authorized_grant :
    kstep demoPolicy initState
      { initState with caps := insert (3, 7) initState.caps } := by
  have : demoPolicy.capAuth 3 7 := by decide
  exact kstep.grantCap 2 3 7 this

/-- An authorized memory write: subject `4` writes address `10` (allowed — the
    even-address restriction only binds subject `0`).  The step fires. -/
theorem demo_authorized_write :
    kstep demoPolicy initState
      { initState with
        mem    := Function.update initState.mem 10 99
        writer := Function.update initState.writer 10 (some 4) } := by
  have : demoPolicy.writeAuth 4 10 := by decide
  exact kstep.writeMem 4 10 99 this

/-- An authorized IPC send: subject `1` sends to subject `5` on endpoint `8`
    (`1 ≤ 8` and `5 ≤ 8`).  The step fires. -/
theorem demo_authorized_send :
    kstep demoPolicy initState
      { initState with
        mailbox :=
          Function.update initState.mailbox 5 (⟨1, 8, 42⟩ :: initState.mailbox 5) } := by
  have hs : demoPolicy.sendAuth 1 8 := by decide
  have hr : demoPolicy.recvAuth 5 8 := by decide
  exact kstep.sendMsg 1 8 5 42 hs hr

/-- The state after the authorized grant is still secure — the composite invariant
    survives a real transition. -/
theorem demo_grant_preserves_secure :
    KernelSecure demoPolicy { initState with caps := insert (3, 7) initState.caps } :=
  kstep_preserves demoPolicy demo_authorized_grant initState_secure

/-- The state after the authorized write is still secure. -/
theorem demo_write_preserves_secure :
    KernelSecure demoPolicy
      { initState with
        mem    := Function.update initState.mem 10 99
        writer := Function.update initState.writer 10 (some 4) } :=
  kstep_preserves demoPolicy demo_authorized_write initState_secure

/-- The composite state reached by all three authorized ops in sequence is secure,
    via the full reachability theorem — the invariant holds across a multi-step run. -/
theorem demo_reachable_secure :
    KernelSecure demoPolicy
      { initState with
        caps    := insert (3, 7) initState.caps
        mem     := Function.update initState.mem 10 99
        writer  := Function.update initState.writer 10 (some 4)
        mailbox :=
          Function.update initState.mailbox 5 (⟨1, 8, 42⟩ :: initState.mailbox 5) } := by
  have r0 : Reachable demoPolicy initState initState := Relation.ReflTransGen.refl
  -- step 1: authorized grant
  have s1 := { initState with caps := insert (3, 7) initState.caps }
  have r1 : Reachable demoPolicy initState
      { initState with caps := insert (3, 7) initState.caps } :=
    Relation.ReflTransGen.tail r0 demo_authorized_grant
  -- step 2: authorized write from s1
  have step2 :
      kstep demoPolicy { initState with caps := insert (3, 7) initState.caps }
        { initState with
          caps   := insert (3, 7) initState.caps
          mem    := Function.update initState.mem 10 99
          writer := Function.update initState.writer 10 (some 4) } := by
    have hw : demoPolicy.writeAuth 4 10 := by decide
    exact kstep.writeMem 4 10 99 hw
  have r2 : Reachable demoPolicy initState
      { initState with
        caps   := insert (3, 7) initState.caps
        mem    := Function.update initState.mem 10 99
        writer := Function.update initState.writer 10 (some 4) } :=
    Relation.ReflTransGen.tail r1 step2
  -- step 3: authorized send
  have step3 :
      kstep demoPolicy
        { initState with
          caps   := insert (3, 7) initState.caps
          mem    := Function.update initState.mem 10 99
          writer := Function.update initState.writer 10 (some 4) }
        { initState with
          caps    := insert (3, 7) initState.caps
          mem     := Function.update initState.mem 10 99
          writer  := Function.update initState.writer 10 (some 4)
          mailbox :=
            Function.update initState.mailbox 5 (⟨1, 8, 42⟩ :: initState.mailbox 5) } := by
    have hs : demoPolicy.sendAuth 1 8 := by decide
    have hr : demoPolicy.recvAuth 5 8 := by decide
    exact kstep.sendMsg 1 8 5 42 hs hr
  have r3 : Reachable demoPolicy initState
      { initState with
        caps    := insert (3, 7) initState.caps
        mem     := Function.update initState.mem 10 99
        writer  := Function.update initState.writer 10 (some 4)
        mailbox :=
          Function.update initState.mailbox 5 (⟨1, 8, 42⟩ :: initState.mailbox 5) } :=
    Relation.ReflTransGen.tail r2 step3
  exact kernel_security demoPolicy _ _ initState_secure r3

/-! ### (b) The guard blocks unauthorized operations. -/

/-- `(5, 3)` is a *forbidden* capability (`5 ≤ 3` is false), so no kernel step can
    ever insert it.  There is no rule that fires with an unauthorized cap. -/
theorem demo_bad_cap_blocked :
    ¬ demoPolicy.capAuth 5 3 := by decide

/-- Subject `0` writing an *odd* address is unauthorized, so the guard forbids it. -/
theorem demo_bad_write_blocked :
    ¬ demoPolicy.writeAuth 0 7 := by decide

/-- An unauthorized send (`7 ≤ 3` false) is forbidden by the send guard. -/
theorem demo_bad_send_blocked :
    ¬ demoPolicy.sendAuth 7 3 := by decide

/-! ### (c) A concrete off-policy state is provably unreachable. -/

/-- An off-policy state that holds the forbidden capability `(5, 3)`. -/
def badState : KernelState where
  caps    := {(5, 3)}
  mem     := fun _ => 0
  writer  := fun _ => none
  mailbox := fun _ => []

/-- `badState` violates the composite security policy: it holds an out-of-authority
    capability. -/
theorem badState_insecure : ¬ KernelSecure demoPolicy badState := by
  intro h
  have := h.1 (5, 3) (by decide)
  exact demo_bad_cap_blocked this

/-- **Unreachability.**  `badState` can never be reached from the secure initial
    state — because every reachable state is secure but `badState` is not.  This is
    the security guarantee turned into a concrete negative: the kernel model forbids
    the off-policy configuration entirely. -/
theorem badState_unreachable :
    ¬ Reachable demoPolicy initState badState := by
  intro hreach
  exact badState_insecure (kernel_security demoPolicy initState badState initState_secure hreach)


/-! ## Capstone extension: a new reference-monitor operation (message consumption) -/

/-- The **extended** kernel step relation: every guarded operation of `kstep`, PLUS a
new `recvMsg` rule — a subject consuming (removing) the head message of its OWN
mailbox.  Consumption is unconditionally safe: it only ever shrinks a mailbox. -/
inductive kstepExt (P : Policy) : KernelState → KernelState → Prop
  | base {s s' : KernelState} (h : kstep P s s') : kstepExt P s s'
  | recvMsg (subj : Subject) (st : KernelState) :
      kstepExt P st
        { st with mailbox := Function.update st.mailbox subj (st.mailbox subj).tail }

/-- Reachability under the extended reference monitor. -/
def ReachableExt (P : Policy) : KernelState → KernelState → Prop :=
  Relation.ReflTransGen (kstepExt P)

/-- One-step preservation for the EXTENDED monitor.  The base steps preserve security
by `kstep_preserves`; message consumption preserves it because the tail of a mailbox
is a sublist of the original, so every remaining message was already authorized. -/
theorem kstepExt_preserves (P : Policy) {s s' : KernelState}
    (hstep : kstepExt P s s') (hinv : KernelSecure P s) : KernelSecure P s' := by
  cases hstep with
  | base h => exact kstep_preserves P h hinv
  | recvMsg subj st =>
      obtain ⟨hcaps, hwrite, hmail⟩ := hinv
      refine ⟨hcaps, hwrite, ?_⟩
      intro dst d hd
      dsimp only at hd
      by_cases hs : dst = subj
      · subst hs
        rw [Function.update_self] at hd
        exact hmail dst d (List.mem_of_mem_tail hd)
      · rw [Function.update_of_ne hs] at hd
        exact hmail dst d hd

/-- **The extended capstone.**  The whole composite security policy is preserved
across *every* reachable state of the extended kernel — guarded operations AND
message consumption — from any policy-conformant start. -/
theorem kernel_security_ext (P : Policy) (s0 s : KernelState)
    (h0 : KernelSecure P s0) (hreach : ReachableExt P s0 s) : KernelSecure P s := by
  induction hreach with
  | refl => exact h0
  | tail _ hstep ih => exact kstepExt_preserves P hstep ih

/-- Message consumption is a strict refinement of the kernel's security guarantee: it
is a new top-level operation shown safe without weakening any of the three security
dimensions. -/
theorem recv_preserves_all (P : Policy) (s : KernelState) (subj : Subject)
    (hinv : KernelSecure P s) :
    KernelSecure P { s with mailbox := Function.update s.mailbox subj (s.mailbox subj).tail } :=
  kstepExt_preserves P (kstepExt.recvMsg subj s) hinv

end Brockian.HighAssurance.Kernel
