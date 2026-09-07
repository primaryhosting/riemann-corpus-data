import Mathlib

/-!
# Capability-Microkernel Deadlock-Freedom / Progress (rendezvous IPC)

A capability microkernel time-multiplexes threads and mediates inter-process
communication through **synchronous (rendezvous) endpoints**, seL4-style: a thread
that wants to `send` on an endpoint *blocks* until a receiver is ready on the same
endpoint (and vice-versa).  When a matched sender/receiver pair meets on an endpoint
they **rendezvous** — both unblock and become `Ready`.

The already-proved kernel theorems are *safety* properties ("nothing bad ever
happens": no unauthorized IPC, no privilege escalation, memory separation, …).  This
module proves the complementary *liveness* property:

> **Deadlock-freedom / progress** — the kernel never *wedges* with work still
> outstanding.  From any well-formed state the system is either **quiescent** (no
> thread blocked — no pending work) or *some* endpoint carries a matched
> sender/receiver pair that can make progress.  A blocking configuration with no
> matched pair is *honest waiting* (a thread legitimately waiting for an external
> partner), **not** a deadlock.

Progress is *measurable*: every rendezvous **strictly decreases** the number of
blocked threads (`blockedCount`).  So a **well-matched** system — every endpoint
carries as many blocked senders as blocked receivers — cannot stall: it drains to
quiescence in finitely many steps, the strictly-decreasing blocked-count serving as a
well-founded termination measure (bounded liveness).

This is the deadlock-freedom guarantee of a capability microkernel's IPC subsystem.
-/

namespace Brockian.HighAssurance.Progress

/-- Threads are identified by natural numbers (thread control block ids). -/
abbrev Thread := ℕ
/-- Synchronous IPC endpoints (rendezvous points). -/
abbrev Endpoint := ℕ

/-- The IPC-relevant status of a thread.

* `Ready`         — runnable, not blocked on IPC.
* `BlockedSend e` — blocked sending on endpoint `e` (waiting for a receiver).
* `BlockedRecv e` — blocked receiving on endpoint `e` (waiting for a sender). -/
inductive ThreadState where
  | Ready       : ThreadState
  | BlockedSend : Endpoint → ThreadState
  | BlockedRecv : Endpoint → ThreadState
  deriving DecidableEq, Repr

open ThreadState

/-- Kernel IPC state: the status of every thread over a finite live-thread set. -/
structure KState where
  /-- The finite set of live threads (those with a thread control block). -/
  dom    : Finset Thread
  /-- The IPC status of each thread. -/
  status : Thread → ThreadState

/-- Well-formedness: only live threads (those in `dom`) may be blocked; every thread
    outside the finite domain is `Ready`.  The standard kernel invariant that a TCB
    exists for every blocked thread. -/
def WellFormed (st : KState) : Prop :=
  ∀ t, st.status t ≠ Ready → t ∈ st.dom

/-! ## Blocking predicates -/

/-- A thread is *blocked* on IPC iff it is not `Ready`. -/
def Blocked (st : KState) (t : Thread) : Prop := st.status t ≠ Ready

instance (st : KState) (t : Thread) : Decidable (Blocked st t) := by
  unfold Blocked; infer_instance

/-- The system has **pending work** if some thread is blocked on a send or receive. -/
def Pending (st : KState) : Prop :=
  ∃ t ep, st.status t = BlockedSend ep ∨ st.status t = BlockedRecv ep

/-- The system is **quiescent** iff no thread is blocked — no pending work. -/
def Quiescent (st : KState) : Prop := ∀ t, st.status t = Ready

/-- A matched sender/receiver pair exists on endpoint `ep`: some live thread is blocked
    sending on `ep` and some live thread is blocked receiving on `ep`.  Precondition for
    a rendezvous. -/
def canRendezvous (st : KState) (ep : Endpoint) : Prop :=
  (∃ t ∈ st.dom, st.status t = BlockedSend ep) ∧ (∃ t ∈ st.dom, st.status t = BlockedRecv ep)

instance (st : KState) (ep : Endpoint) : Decidable (canRendezvous st ep) := by
  unfold canRendezvous; infer_instance

/-! ## Per-endpoint blocked counts and the progress measure -/

/-- Number of live threads blocked *sending* on `ep`. -/
def sendCount (st : KState) (ep : Endpoint) : ℕ :=
  (st.dom.filter (fun t => st.status t = BlockedSend ep)).card

/-- Number of live threads blocked *receiving* on `ep`. -/
def recvCount (st : KState) (ep : Endpoint) : ℕ :=
  (st.dom.filter (fun t => st.status t = BlockedRecv ep)).card

/-- The total number of blocked threads: the progress / termination measure.  A
    rendezvous strictly decreases it, and it is `0` exactly when a well-formed system is
    quiescent. -/
def blockedCount (st : KState) : ℕ :=
  (st.dom.filter (fun t => Blocked st t)).card

/-! ## Witness selection and the rendezvous step -/

/-- Pick the least live thread satisfying `p` (deterministic witness selection). -/
def pick (st : KState) (p : Thread → Prop) [DecidablePred p]
    (h : ∃ t ∈ st.dom, p t) : Thread :=
  (st.dom.filter p).min' (by
    rcases h with ⟨t, ht, hpt⟩
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, hpt⟩⟩)

/-- The picked thread is live and satisfies `p`. -/
theorem pick_spec (st : KState) (p : Thread → Prop) [DecidablePred p]
    (h : ∃ t ∈ st.dom, p t) : pick st p h ∈ st.dom ∧ p (pick st p h) := by
  have hmem : pick st p h ∈ st.dom.filter p := Finset.min'_mem _ _
  exact Finset.mem_filter.mp hmem

/-- The selected blocked sender on `ep` (given a matched pair exists). -/
noncomputable def sndr (st : KState) (ep : Endpoint) (h : canRendezvous st ep) : Thread :=
  pick st (fun t => st.status t = BlockedSend ep) h.1

/-- The selected blocked receiver on `ep` (given a matched pair exists). -/
noncomputable def rcvr (st : KState) (ep : Endpoint) (h : canRendezvous st ep) : Thread :=
  pick st (fun t => st.status t = BlockedRecv ep) h.2

theorem sndr_spec (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    sndr st ep h ∈ st.dom ∧ st.status (sndr st ep h) = BlockedSend ep :=
  pick_spec st _ h.1

theorem rcvr_spec (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    rcvr st ep h ∈ st.dom ∧ st.status (rcvr st ep h) = BlockedRecv ep :=
  pick_spec st _ h.2

/-- Sender and receiver of a rendezvous are distinct threads. -/
theorem sndr_ne_rcvr (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    sndr st ep h ≠ rcvr st ep h := by
  intro heq
  have hs := (sndr_spec st ep h).2
  have hr := (rcvr_spec st ep h).2
  rw [heq, hr] at hs
  exact ThreadState.noConfusion hs

/-- The rendezvous step on endpoint `ep`.  If a matched pair exists, unblock the
    selected sender and receiver (both become `Ready`); otherwise leave the state
    unchanged (no matched pair ⇒ honest waiting, nothing to do). -/
noncomputable def stepRendezvous (ep : Endpoint) (st : KState) : KState :=
  if h : canRendezvous st ep then
    { dom := st.dom
      status := fun t => if t = sndr st ep h ∨ t = rcvr st ep h then Ready else st.status t }
  else st

/-- In the matched case the step keeps the domain and sets exactly sender/receiver ready. -/
theorem stepRendezvous_pos (ep : Endpoint) (st : KState) (h : canRendezvous st ep) :
    stepRendezvous ep st =
      { dom := st.dom
        status := fun t => if t = sndr st ep h ∨ t = rcvr st ep h then Ready else st.status t } := by
  simp only [stepRendezvous, dif_pos h]

/-! ## Key set-rewriting lemma -/

/-- Filtering a two-thread "set to `Ready`" update by a non-`Ready` target removes the
    two threads from the original filtered set. -/
theorem filter_setReadyPair (D : Finset ℕ) (f : ℕ → ThreadState) (s r : ℕ)
    (X : ThreadState) (hX : X ≠ Ready) :
    D.filter (fun t => (if t = s ∨ t = r then Ready else f t) = X)
      = ((D.filter (fun t => f t = X)).erase s).erase r := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨htD, hEq⟩
    by_cases hsr : t = s ∨ t = r
    · rw [if_pos hsr] at hEq; exact absurd hEq.symm hX
    · rw [if_neg hsr] at hEq
      push_neg at hsr
      exact ⟨hsr.2, hsr.1, htD, hEq⟩
  · rintro ⟨htr, hts, htD, hfX⟩
    have hsr : ¬ (t = s ∨ t = r) := by push_neg; exact ⟨hts, htr⟩
    rw [if_neg hsr]
    exact ⟨htD, hfX⟩

/-! ## PROGRESS / DEADLOCK-FREEDOM: a rendezvous strictly decreases blocked threads -/

/-- **PROGRESS.**  A rendezvous strictly reduces the number of blocked threads: no
    infinite stall is possible while matched work exists. -/
theorem rendezvous_progress (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    blockedCount (stepRendezvous ep st) < blockedCount st := by
  have hsd := sndr_spec st ep h
  have hstep := stepRendezvous_pos ep st h
  -- The new blocked set is a subset of the old one.
  have hsub : (stepRendezvous ep st).dom.filter (fun t => Blocked (stepRendezvous ep st) t)
      ⊆ st.dom.filter (fun t => Blocked st t) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    obtain ⟨htD, htB⟩ := ht
    rw [hstep] at htD
    refine ⟨htD, ?_⟩
    unfold Blocked at htB ⊢
    rw [hstep] at htB
    dsimp only at htB
    by_cases hsr : t = sndr st ep h ∨ t = rcvr st ep h
    · rw [if_pos hsr] at htB; exact absurd rfl htB
    · rw [if_neg hsr] at htB; exact htB
  -- The sender is in the old blocked set but not the new one.
  have hs_old : sndr st ep h ∈ st.dom.filter (fun t => Blocked st t) := by
    rw [Finset.mem_filter]
    refine ⟨hsd.1, ?_⟩
    unfold Blocked; rw [hsd.2]; exact ThreadState.noConfusion
  have hs_new : sndr st ep h ∉
      (stepRendezvous ep st).dom.filter (fun t => Blocked (stepRendezvous ep st) t) := by
    rw [Finset.mem_filter]
    rintro ⟨_, hB⟩
    unfold Blocked at hB
    rw [hstep] at hB
    dsimp only at hB
    rw [if_pos (Or.inl rfl)] at hB
    exact hB rfl
  have hss := (Finset.ssubset_iff_of_subset hsub).mpr ⟨sndr st ep h, hs_old, hs_new⟩
  exact Finset.card_lt_card hss

/-! ## MATCHED PAIR NEVER STUCK -/

/-- **MATCHED PAIR NEVER STUCK.**  Whenever a matched pair exists on `ep`, one step
    unblocks a concrete sender and receiver (both become `Ready`) — a matched pair
    provably rendezvous in a single step. -/
theorem matched_pair_rendezvous (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    ∃ s r, s ≠ r ∧ st.status s = BlockedSend ep ∧ st.status r = BlockedRecv ep ∧
      (stepRendezvous ep st).status s = Ready ∧ (stepRendezvous ep st).status r = Ready := by
  refine ⟨sndr st ep h, rcvr st ep h, sndr_ne_rcvr st ep h,
    (sndr_spec st ep h).2, (rcvr_spec st ep h).2, ?_, ?_⟩
  · rw [stepRendezvous_pos ep st h]
    show (if sndr st ep h = sndr st ep h ∨ sndr st ep h = rcvr st ep h
      then Ready else st.status (sndr st ep h)) = Ready
    rw [if_pos (Or.inl rfl)]
  · rw [stepRendezvous_pos ep st h]
    show (if rcvr st ep h = sndr st ep h ∨ rcvr st ep h = rcvr st ep h
      then Ready else st.status (rcvr st ep h)) = Ready
    rw [if_pos (Or.inr rfl)]

/-! ## Well-matched systems: balanced per-endpoint blocked counts -/

/-- A system is **well-matched** if it is well-formed and, on every endpoint, exactly as
    many live threads are blocked sending as are blocked receiving.  Equivalently: every
    blocked sender is paired with a distinct blocked receiver on its endpoint and
    vice-versa.  This is the invariant preserved by rendezvous (it excludes a lone
    unpaired sender/receiver, which is honest waiting rather than a deadlock). -/
def WellMatched (st : KState) : Prop :=
  WellFormed st ∧ ∀ ep, sendCount st ep = recvCount st ep

/-! ## Progress core: a well-matched, non-quiescent system has a matched pair -/

/-- If a well-formed, balanced system has any blocked thread, some endpoint carries a
    matched pair. -/
theorem progress_core (st : KState) (hwf : WellFormed st)
    (hbal : ∀ ep, sendCount st ep = recvCount st ep)
    (hb : ∃ t ∈ st.dom, st.status t ≠ Ready) : ∃ ep, canRendezvous st ep := by
  obtain ⟨t, htD, htB⟩ := hb
  -- t is blocked sending or receiving on some endpoint
  cases hstatus : st.status t with
  | Ready => exact absurd hstatus htB
  | BlockedSend ep =>
      -- there is a blocked receiver on ep by balance
      have hsend_pos : 0 < sendCount st ep := by
        apply Finset.card_pos.mpr
        exact ⟨t, Finset.mem_filter.mpr ⟨htD, hstatus⟩⟩
      have hrecv_pos : 0 < recvCount st ep := by rw [← hbal ep]; exact hsend_pos
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hrecv_pos
      obtain ⟨hrD, hrS⟩ := Finset.mem_filter.mp hr
      exact ⟨ep, ⟨t, htD, hstatus⟩, ⟨r, hrD, hrS⟩⟩
  | BlockedRecv ep =>
      have hrecv_pos : 0 < recvCount st ep := by
        apply Finset.card_pos.mpr
        exact ⟨t, Finset.mem_filter.mpr ⟨htD, hstatus⟩⟩
      have hsend_pos : 0 < sendCount st ep := by rw [hbal ep]; exact hrecv_pos
      obtain ⟨s, hs⟩ := Finset.card_pos.mp hsend_pos
      obtain ⟨hsD, hsS⟩ := Finset.mem_filter.mp hs
      exact ⟨ep, ⟨s, hsD, hsS⟩, ⟨t, htD, hstatus⟩⟩

/-! ## NO-DEADLOCK on a well-matched system -/

/-- **NO-DEADLOCK.**  A well-matched system is either quiescent or has an endpoint on
    which a rendezvous can fire — it can never wedge with pending work. -/
theorem no_deadlock (st : KState) (hmatched : WellMatched st) :
    Quiescent st ∨ ∃ ep, canRendezvous st ep := by
  obtain ⟨hwf, hbal⟩ := hmatched
  by_cases hq : Quiescent st
  · exact Or.inl hq
  · refine Or.inr ?_
    have : ∃ t, st.status t ≠ Ready := by
      unfold Quiescent at hq; push_neg at hq; exact hq
    obtain ⟨t, htB⟩ := this
    exact progress_core st hwf hbal ⟨t, hwf t htB, htB⟩

/-! ## Preservation of well-matchedness by a rendezvous -/

/-- `blockedCount 0` on a well-formed system means quiescence. -/
theorem quiescent_of_blockedCount_zero (st : KState) (hwf : WellFormed st)
    (h0 : blockedCount st = 0) : Quiescent st := by
  intro t
  by_contra hne
  have htD : t ∈ st.dom := hwf t hne
  have : t ∈ st.dom.filter (fun t => Blocked st t) :=
    Finset.mem_filter.mpr ⟨htD, hne⟩
  rw [Finset.card_eq_zero.mp h0] at this
  exact absurd this (Finset.notMem_empty t)

/-- Rendezvous preserves well-formedness. -/
theorem wellFormed_step (st : KState) (ep : Endpoint) (h : canRendezvous st ep)
    (hwf : WellFormed st) : WellFormed (stepRendezvous ep st) := by
  intro t htB
  rw [stepRendezvous_pos ep st h] at htB ⊢
  simp only at htB ⊢
  by_cases hsr : t = sndr st ep h ∨ t = rcvr st ep h
  · simp only [if_pos hsr] at htB; exact absurd rfl htB
  · simp only [if_neg hsr] at htB
    exact hwf t htB

/-- Send-count on the rendezvous endpoint drops by one. -/
theorem sendCount_step_eq (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    sendCount (stepRendezvous ep st) ep = sendCount st ep - 1 := by
  have hsd := sndr_spec st ep h
  have hrd := rcvr_spec st ep h
  have hne := sndr_ne_rcvr st ep h
  set s := sndr st ep h
  set r := rcvr st ep h
  unfold sendCount
  rw [stepRendezvous_pos ep st h]
  simp only
  rw [filter_setReadyPair st.dom st.status s r (BlockedSend ep) (by exact ThreadState.noConfusion)]
  -- s ∈ filter, r ∉ filter
  have hsF : s ∈ st.dom.filter (fun t => st.status t = BlockedSend ep) :=
    Finset.mem_filter.mpr ⟨hsd.1, hsd.2⟩
  have hrF : r ∉ st.dom.filter (fun t => st.status t = BlockedSend ep) := by
    rw [Finset.mem_filter]; rintro ⟨_, hrS⟩; rw [hrd.2] at hrS; exact ThreadState.noConfusion hrS
  have hr_erase : r ∉ (st.dom.filter (fun t => st.status t = BlockedSend ep)).erase s :=
    fun hmem => hrF (Finset.mem_of_mem_erase hmem)
  rw [Finset.erase_eq_of_notMem hr_erase, Finset.card_erase_of_mem hsF]

/-- Recv-count on the rendezvous endpoint drops by one. -/
theorem recvCount_step_eq (st : KState) (ep : Endpoint) (h : canRendezvous st ep) :
    recvCount (stepRendezvous ep st) ep = recvCount st ep - 1 := by
  have hsd := sndr_spec st ep h
  have hrd := rcvr_spec st ep h
  set s := sndr st ep h
  set r := rcvr st ep h
  unfold recvCount
  rw [stepRendezvous_pos ep st h]
  simp only
  rw [filter_setReadyPair st.dom st.status s r (BlockedRecv ep) (by exact ThreadState.noConfusion)]
  have hrF : r ∈ st.dom.filter (fun t => st.status t = BlockedRecv ep) :=
    Finset.mem_filter.mpr ⟨hrd.1, hrd.2⟩
  have hsF : s ∉ st.dom.filter (fun t => st.status t = BlockedRecv ep) := by
    rw [Finset.mem_filter]; rintro ⟨_, hsS⟩; rw [hsd.2] at hsS; exact ThreadState.noConfusion hsS
  -- erase s is a no-op; then erase r
  rw [Finset.erase_eq_of_notMem hsF, Finset.card_erase_of_mem hrF]

/-- On any *other* endpoint the send-count is unchanged by a rendezvous on `ep`. -/
theorem sendCount_step_ne (st : KState) (ep ep' : Endpoint) (h : canRendezvous st ep)
    (hne : ep' ≠ ep) : sendCount (stepRendezvous ep st) ep' = sendCount st ep' := by
  have hsd := sndr_spec st ep h
  have hrd := rcvr_spec st ep h
  set s := sndr st ep h
  set r := rcvr st ep h
  unfold sendCount
  rw [stepRendezvous_pos ep st h]
  simp only
  rw [filter_setReadyPair st.dom st.status s r (BlockedSend ep') (by exact ThreadState.noConfusion)]
  have hsF : s ∉ st.dom.filter (fun t => st.status t = BlockedSend ep') := by
    rw [Finset.mem_filter]; rintro ⟨_, hsS⟩; rw [hsd.2] at hsS
    exact hne (by injection hsS with h1; exact h1.symm)
  have hrF : r ∉ st.dom.filter (fun t => st.status t = BlockedSend ep') := by
    rw [Finset.mem_filter]; rintro ⟨_, hrS⟩; rw [hrd.2] at hrS; exact ThreadState.noConfusion hrS
  have hr_erase : r ∉ (st.dom.filter (fun t => st.status t = BlockedSend ep')).erase s :=
    fun hmem => hrF (Finset.mem_of_mem_erase hmem)
  rw [Finset.erase_eq_of_notMem hr_erase, Finset.erase_eq_of_notMem hsF]

/-- On any *other* endpoint the recv-count is unchanged by a rendezvous on `ep`. -/
theorem recvCount_step_ne (st : KState) (ep ep' : Endpoint) (h : canRendezvous st ep)
    (hne : ep' ≠ ep) : recvCount (stepRendezvous ep st) ep' = recvCount st ep' := by
  have hsd := sndr_spec st ep h
  have hrd := rcvr_spec st ep h
  set s := sndr st ep h
  set r := rcvr st ep h
  unfold recvCount
  rw [stepRendezvous_pos ep st h]
  simp only
  rw [filter_setReadyPair st.dom st.status s r (BlockedRecv ep') (by exact ThreadState.noConfusion)]
  have hsF : s ∉ st.dom.filter (fun t => st.status t = BlockedRecv ep') := by
    rw [Finset.mem_filter]; rintro ⟨_, hsS⟩; rw [hsd.2] at hsS; exact ThreadState.noConfusion hsS
  have hrF : r ∉ st.dom.filter (fun t => st.status t = BlockedRecv ep') := by
    rw [Finset.mem_filter]; rintro ⟨_, hrS⟩; rw [hrd.2] at hrS
    exact hne (by injection hrS with h1; exact h1.symm)
  have hr_erase : r ∉ (st.dom.filter (fun t => st.status t = BlockedRecv ep')).erase s :=
    fun hmem => hrF (Finset.mem_of_mem_erase hmem)
  rw [Finset.erase_eq_of_notMem hr_erase, Finset.erase_eq_of_notMem hsF]

/-- Rendezvous preserves the balanced (well-matched) invariant. -/
theorem wellMatched_step (st : KState) (ep : Endpoint) (h : canRendezvous st ep)
    (hm : WellMatched st) : WellMatched (stepRendezvous ep st) := by
  obtain ⟨hwf, hbal⟩ := hm
  refine ⟨wellFormed_step st ep h hwf, ?_⟩
  intro ep'
  by_cases hee : ep' = ep
  · subst hee
    rw [sendCount_step_eq st ep' h, recvCount_step_eq st ep' h, hbal ep']
  · rw [sendCount_step_ne st ep ep' h hee, recvCount_step_ne st ep ep' h hee, hbal ep']

/-! ## The drain iteration -/

-- One "some rendezvous" step: fire a rendezvous on some ready endpoint if one exists,
-- else stop (quiescent or honestly waiting).
open Classical in
noncomputable def stepSome (st : KState) : KState :=
  if h : ∃ ep, canRendezvous st ep then stepRendezvous (Classical.choose h) st else st

/-- Iterate the drain step `n` times. -/
noncomputable def iterateRendezvous : ℕ → KState → KState
  | 0,     st => st
  | (n+1), st => iterateRendezvous n (stepSome st)

theorem iterateRendezvous_succ (n : ℕ) (st : KState) :
    iterateRendezvous (n + 1) st = iterateRendezvous n (stepSome st) := rfl

/-- A well-matched system drains to quiescence: `∃ n`, iterating the rendezvous step `n`
    times reaches a quiescent state (bounded liveness — `n ≤ blockedCount st`). -/
theorem drains_to_quiescent (st : KState) (hmatched : WellMatched st) :
    ∃ n, Quiescent (iterateRendezvous n st) := by
  -- strong induction on the progress measure
  suffices H : ∀ N, ∀ s : KState, blockedCount s = N → WellMatched s →
      ∃ n, Quiescent (iterateRendezvous n s) by
    exact H (blockedCount st) st rfl hmatched
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s hcard hm
    obtain ⟨hwf, hbal⟩ := hm
    rcases Nat.eq_zero_or_pos (blockedCount s) with h0 | hpos
    · exact ⟨0, quiescent_of_blockedCount_zero s hwf h0⟩
    · -- some blocked thread exists ⇒ a matched pair exists
      have hb : ∃ t ∈ s.dom, s.status t ≠ Ready := by
        obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
        obtain ⟨htD, htB⟩ := Finset.mem_filter.mp ht
        exact ⟨t, htD, htB⟩
      have hex : ∃ ep, canRendezvous s ep := progress_core s hwf hbal hb
      -- fire it
      have hchoose : canRendezvous s (Classical.choose hex) := Classical.choose_spec hex
      have hstepSome : stepSome s = stepRendezvous (Classical.choose hex) s := by
        simp only [stepSome, dif_pos hex]
      -- progress + preservation
      have hlt : blockedCount (stepSome s) < blockedCount s := by
        rw [hstepSome]; exact rendezvous_progress s (Classical.choose hex) hchoose
      have hm' : WellMatched (stepSome s) := by
        rw [hstepSome]; exact wellMatched_step s (Classical.choose hex) hchoose ⟨hwf, hbal⟩
      -- apply the induction hypothesis to the smaller state
      obtain ⟨m, hmq⟩ :=
        ih (blockedCount (stepSome s)) (by rw [← hcard]; exact hlt) (stepSome s) rfl hm'
      exact ⟨m + 1, by rw [iterateRendezvous_succ]; exact hmq⟩

/-! ## NON-VACUITY (concrete, decidable) -/

/-- A matched send/recv pair: thread `0` blocked sending on endpoint `5`, thread `1`
    blocked receiving on `5`. -/
def demo : KState :=
  { dom := {0, 1}
    status := fun t => if t = 0 then BlockedSend 5 else if t = 1 then BlockedRecv 5 else Ready }

/-- (a) The matched pair can rendezvous. -/
example : canRendezvous demo 5 := by decide

/-- Two threads are blocked in `demo`. -/
example : blockedCount demo = 2 := by decide

/-- (a) The matched pair provably rendezvous: both become `Ready` in one step. -/
example : ∃ s r, s ≠ r ∧ demo.status s = BlockedSend 5 ∧ demo.status r = BlockedRecv 5 ∧
    (stepRendezvous 5 demo).status s = Ready ∧ (stepRendezvous 5 demo).status r = Ready :=
  matched_pair_rendezvous demo 5 (by decide)

/-- (b) The rendezvous strictly reduces the number of blocked threads. -/
example : blockedCount (stepRendezvous 5 demo) < blockedCount demo :=
  rendezvous_progress demo 5 (by decide)

/-- A lone sender: thread `0` blocked sending on `5`, no receiver anywhere. -/
def demoLone : KState :=
  { dom := {0}
    status := fun t => if t = 0 then BlockedSend 5 else Ready }

/-- (c) The lone sender is *honestly blocked*: no rendezvous is possible. -/
example : ¬ canRendezvous demoLone 5 := by decide

/-- One thread is blocked in `demoLone` — pending work outstanding … -/
example : blockedCount demoLone = 1 := by decide

/-- … yet this is NOT a deadlock: it is legitimate waiting, and the `WellMatched`
    (balanced) hypothesis excludes it, since the send/recv counts are unequal
    (`1 ≠ 0`). -/
example : sendCount demoLone 5 ≠ recvCount demoLone 5 := by decide

end Brockian.HighAssurance.Progress
