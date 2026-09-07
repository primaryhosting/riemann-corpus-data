import Mathlib

/-!
# Capability-Gated IPC Confinement (seL4-style endpoints)

A capability microkernel mediates inter-process communication through *endpoints*.
A subject may `send` to an endpoint only if it holds a `sendCap` for it, and a
message is delivered to a subject only if that subject holds a `recvCap` for the
endpoint the message traversed.  These two capabilities are the *static
communication policy*.

We model IPC as a small-step operation over per-subject mailboxes and prove the
**communication-integrity** property of the microkernel:

> Every message that ends up in a subject's mailbox traversed an *authorized
> channel* — there is an endpoint on which the receiver holds `recvCap` and some
> sender held `sendCap`.  No message crosses an unauthorized boundary.

This is the IPC-confinement guarantee of a capability system (cf. seL4 endpoints).
-/

namespace Brockian.HighAssurance.IPCConfinement

/-- Subjects (threads / processes). -/
abbrev Subject := ℕ
/-- Communication endpoints (seL4 endpoint capabilities point at these). -/
abbrev Endpoint := ℕ
/-- Messages. -/
abbrev Msg := ℕ
/-- A mailbox state: the list of messages each subject has been delivered. -/
abbrev Mailbox := Subject → List Msg

/-- A single IPC operation: `frm` sends message `m` to `dst` via endpoint `ep`.
    (`dst` is the destination subject — `to` is a reserved word in Lean 4.) -/
structure IPCOp where
  frm : Subject
  ep  : Endpoint
  dst : Subject
  m   : Msg

/-! ## Static communication policy (capabilities) -/

variable (sendCap recvCap : Subject → Endpoint → Prop)
variable [∀ s e, Decidable (sendCap s e)]
variable [∀ s e, Decidable (recvCap s e)]

/--
The kernel's IPC step.  The message is delivered to `dst`'s mailbox **only if**
the sender holds `sendCap` on the endpoint *and* the receiver holds `recvCap` on
the same endpoint (both endpoints of the channel are authorized).  Otherwise the
operation is a no-op — the capability check fails closed.
-/
def stepIPC (op : IPCOp) (mb : Mailbox) : Mailbox :=
  if sendCap op.frm op.ep ∧ recvCap op.dst op.ep then
    Function.update mb op.dst (op.m :: mb op.dst)
  else
    mb

/-- Run a sequence of IPC operations, folding over the list. -/
def run : List IPCOp → Mailbox → Mailbox
  | [],        mb => mb
  | op :: ops, mb => stepIPC sendCap recvCap op (run ops mb)

@[simp] theorem run_nil (mb : Mailbox) : run sendCap recvCap [] mb = mb := rfl

@[simp] theorem run_cons (op : IPCOp) (ops : List IPCOp) (mb : Mailbox) :
    run sendCap recvCap (op :: ops) mb
      = stepIPC sendCap recvCap op (run sendCap recvCap ops mb) := rfl

/-- Point-wise behaviour of a single IPC step. -/
theorem stepIPC_apply (op : IPCOp) (mb : Mailbox) (s : Subject) :
    stepIPC sendCap recvCap op mb s
      = if (sendCap op.frm op.ep ∧ recvCap op.dst op.ep) ∧ s = op.dst
        then op.m :: mb s else mb s := by
  unfold stepIPC
  by_cases hc : sendCap op.frm op.ep ∧ recvCap op.dst op.ep
  · rw [if_pos hc, Function.update_apply]
    by_cases hs : s = op.dst
    · rw [if_pos hs, if_pos ⟨hc, hs⟩, hs]
    · rw [if_neg hs, if_neg (fun h => hs h.2)]
  · rw [if_neg hc, if_neg (fun h => hc h.1)]

/-! ## Theorem 1 — unauthorized send is a no-op -/

/--
A send in which the sender lacks `sendCap` **or** the receiver lacks `recvCap`
leaves *all* mailboxes unchanged.
-/
theorem unauth_send_noop (op : IPCOp) (mb : Mailbox)
    (h : ¬ sendCap op.frm op.ep ∨ ¬ recvCap op.dst op.ep) :
    stepIPC sendCap recvCap op mb = mb := by
  unfold stepIPC
  rw [if_neg]
  rintro ⟨h1, h2⟩
  cases h with
  | inl h => exact h h1
  | inr h => exact h h2

/-! ## Theorem 2 — THE CONFINEMENT THEOREM -/

/--
**IPC confinement.**  If message `m` ends up in subject `dst`'s mailbox and was
not there before, then there is a sender `frm` and an endpoint `ep` such that
`frm` held `sendCap` on `ep`, `dst` held `recvCap` on `ep`, and the authorizing
send operation `⟨frm, ep, dst, m⟩` actually occurred in the op list.

Every newly-delivered message is *explained* by an authorized send: no message
traverses an unauthorized channel.
-/
theorem ipc_confinement (ops : List IPCOp) (mb : Mailbox) (dst : Subject) (m : Msg)
    (hnew : m ∈ run sendCap recvCap ops mb dst ∧ m ∉ mb dst) :
    ∃ (frm : Subject) (ep : Endpoint),
      sendCap frm ep ∧ recvCap dst ep ∧ (⟨frm, ep, dst, m⟩ : IPCOp) ∈ ops := by
  obtain ⟨hin, hnotin⟩ := hnew
  revert hin
  induction ops with
  | nil =>
      intro hin
      rw [run_nil] at hin
      exact absurd hin hnotin
  | cons op ops ih =>
      intro hin
      rw [run_cons, stepIPC_apply] at hin
      by_cases hcond : (sendCap op.frm op.ep ∧ recvCap op.dst op.ep) ∧ dst = op.dst
      · rw [if_pos hcond] at hin
        rcases List.mem_cons.mp hin with heq | hmem
        · -- the message is exactly this send's payload
          refine ⟨op.frm, op.ep, hcond.1.1, ?_, ?_⟩
          · rw [hcond.2]; exact hcond.1.2
          · have hopeq : (⟨op.frm, op.ep, dst, m⟩ : IPCOp) = op := by
              rw [hcond.2, heq]
            rw [hopeq]; exact List.mem_cons.mpr (Or.inl rfl)
        · -- the message was already present after the earlier ops
          obtain ⟨frm, ep, hs, hr, hmemops⟩ := ih hmem
          exact ⟨frm, ep, hs, hr, List.mem_cons.mpr (Or.inr hmemops)⟩
      · rw [if_neg hcond] at hin
        obtain ⟨frm, ep, hs, hr, hmemops⟩ := ih hin
        exact ⟨frm, ep, hs, hr, List.mem_cons.mpr (Or.inr hmemops)⟩

/-! ## Theorem 3 — channel isolation corollary -/

/--
**Channel isolation.**  If subject `dst` shares *no* authorized inbound channel
with any potential sender — i.e. there is no endpoint `ep` for which some sender
holds `sendCap` while `dst` holds `recvCap` — then `dst`'s mailbox never grows,
regardless of the op sequence executed.
-/
theorem no_channel_no_delivery (ops : List IPCOp) (mb : Mailbox) (dst : Subject)
    (hno : ∀ (frm : Subject) (ep : Endpoint), ¬ (sendCap frm ep ∧ recvCap dst ep)) :
    run sendCap recvCap ops mb dst = mb dst := by
  induction ops with
  | nil => rw [run_nil]
  | cons op ops ih =>
      rw [run_cons, stepIPC_apply]
      have hneg : ¬ ((sendCap op.frm op.ep ∧ recvCap op.dst op.ep) ∧ dst = op.dst) := by
        rintro ⟨⟨hsend, hrecv⟩, hdst⟩
        refine hno op.frm op.ep ⟨hsend, ?_⟩
        rw [hdst]; exact hrecv
      rw [if_neg hneg, ih]

/-! ## Non-vacuity — a concrete capability policy -/

section Concrete

/-- Subject `1` may send on endpoint `0`. -/
abbrev csend (s : Subject) (e : Endpoint) : Prop := s = 1 ∧ e = 0
/-- Subject `2` may receive on endpoint `0`. -/
abbrev crecv (s : Subject) (e : Endpoint) : Prop := s = 2 ∧ e = 0

/-- Empty initial state. -/
def emptyMb : Mailbox := fun _ => []

/-- (a) An **authorized** send (both caps held) genuinely delivers the message:
    subject 2's mailbox receives 42 over the authorized 1→(ep 0)→2 channel. -/
theorem nonvacuity_authorized_delivers :
    (42 : Msg) ∈ run csend crecv [⟨1, 0, 2, 42⟩] emptyMb 2 := by
  decide

/-- (b) An **unauthorized** send (receiver 3 lacks `recvCap`) is a provable
    no-op: the entire mailbox state is unchanged. -/
theorem nonvacuity_unauthorized_noop :
    run csend crecv [⟨1, 0, 3, 42⟩] emptyMb = emptyMb := by
  rw [run_cons, run_nil]
  apply unauth_send_noop
  right
  decide

/-- (c) `no_channel_no_delivery` instantiated on the capless subject 3: subject 3
    holds `recvCap` on no endpoint any sender can reach, so no op sequence ever
    delivers to it. -/
theorem nonvacuity_no_channel (ops : List IPCOp) :
    run csend crecv ops emptyMb 3 = emptyMb 3 := by
  apply no_channel_no_delivery
  intro frm ep
  rintro ⟨-, h32, -⟩
  exact absurd h32 (by decide)

end Concrete

end Brockian.HighAssurance.IPCConfinement
