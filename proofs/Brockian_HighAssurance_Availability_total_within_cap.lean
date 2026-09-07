import Mathlib

/-!
# Availability — the third leg of the CIA triad for a capability microkernel

This module formalises **availability** as *resource-reservation / denial-of-service
resistance*, the third of seL4's top-level security properties alongside integrity and
confidentiality (noninterference).

Availability here means: **a subject's guaranteed resources cannot be exhausted by the
activity of other subjects.**  We model a bounded pool of capacity `cap`, a per-subject
reservation `reserved s` (its guaranteed quota), and a runtime state recording each
subject's current `used` amount.  A *non-oversubscription* condition
`∑ s ∈ S, reserved s ≤ cap` says the reservations fit inside the pool.  Guarded
allocation is *fail-closed at the quota* — a subject may allocate only while it is
strictly below its own reservation — and this makes availability structural rather than
best-effort:

* every allocation preserves the well-formedness invariant "no subject exceeds its quota";
* total usage never exceeds the pool capacity;
* a subject with headroom can *always* allocate — its success is independent of what any
  other subject is doing (no cross-subject DoS);
* a subject can allocate its full reservation from empty (bounded liveness / progress).
-/

namespace Brockian.HighAssurance.Availability

/-- Subjects (protection domains) are identified by natural numbers. -/
abbrev Subject := ℕ

/-- Kernel state: the current amount of the pooled resource `used` by each subject.
The state *is* the usage map. -/
abbrev State := Subject → ℕ

/-- Read a subject's current usage out of the state. -/
abbrev used (st : State) : Subject → ℕ := st

/-- **Well-formedness invariant.** No subject in the tracked set `S` exceeds its
reservation.  This is the invariant the guarded operations preserve. -/
def WF (S : Finset Subject) (reserved : Subject → ℕ) (st : State) : Prop :=
  ∀ s ∈ S, used st s ≤ reserved s

/-- **Guarded allocation.** Subject `s` claims one more unit *iff* it is strictly below
its own reservation; otherwise the operation is a no-op (fail-closed at the quota). Only
`s`'s own cell can change. -/
def alloc (reserved : Subject → ℕ) (s : Subject) (st : State) : State :=
  fun t => if t = s ∧ st s < reserved s then st t + 1 else st t

/-- **Release.** Subject `s` gives back one unit (saturating at 0). Only `s`'s cell changes. -/
def free (s : Subject) (st : State) : State :=
  fun t => if t = s then st t - 1 else st t

/-- Kernel operations. -/
inductive Op
  | alloc (s : Subject)
  | free (s : Subject)

/-- One-step transition. -/
def step (reserved : Subject → ℕ) (st : State) : Op → State
  | Op.alloc s => alloc reserved s st
  | Op.free s => free s st

/-- Run a list of operations left to right from a starting state. -/
def run (reserved : Subject → ℕ) : List Op → State → State
  | [], st => st
  | op :: rest, st => run reserved rest (step reserved st op)

/-! ## WF is preserved (no subject ever exceeds its reservation) -/

theorem alloc_preserves_wf (S : Finset Subject) (reserved : Subject → ℕ)
    (s : Subject) (st : State) (hwf : WF S reserved st) :
    WF S reserved (alloc reserved s st) := by
  intro t ht
  show (if t = s ∧ st s < reserved s then st t + 1 else st t) ≤ reserved t
  split
  · rename_i h
    obtain ⟨hts, hlt⟩ := h
    subst hts
    omega
  · exact hwf t ht

theorem free_preserves_wf (S : Finset Subject) (reserved : Subject → ℕ)
    (s : Subject) (st : State) (hwf : WF S reserved st) :
    WF S reserved (free s st) := by
  intro t ht
  show (if t = s then st t - 1 else st t) ≤ reserved t
  split
  · have hle : st t ≤ reserved t := hwf t ht
    omega
  · exact hwf t ht

theorem step_preserves_wf (S : Finset Subject) (reserved : Subject → ℕ)
    (st : State) (op : Op) (hwf : WF S reserved st) :
    WF S reserved (step reserved st op) := by
  cases op with
  | alloc s => exact alloc_preserves_wf S reserved s st hwf
  | free s => exact free_preserves_wf S reserved s st hwf

/-- Run-lifted: any sequence of guarded operations preserves the invariant. -/
theorem run_preserves_wf (S : Finset Subject) (reserved : Subject → ℕ) :
    ∀ (ops : List Op) (st : State), WF S reserved st →
      WF S reserved (run reserved ops st) := by
  intro ops
  induction ops with
  | nil => intro st h; exact h
  | cons op rest ih =>
    intro st h
    exact ih (step reserved st op) (step_preserves_wf S reserved st op h)

/-! ## Capacity is respected (total usage never exceeds the pool) -/

theorem total_within_cap (S : Finset Subject) (reserved : Subject → ℕ) (cap : ℕ)
    (hns : (∑ s ∈ S, reserved s) ≤ cap) (st : State) (hwf : WF S reserved st) :
    (∑ s ∈ S, used st s) ≤ cap := by
  have h1 : (∑ s ∈ S, used st s) ≤ ∑ s ∈ S, reserved s :=
    Finset.sum_le_sum (fun i hi => hwf i hi)
  exact le_trans h1 hns

/-! ## The availability / no-DoS guarantee -/

/-- **Availability guarantee.** A subject that is below its own reservation can *always*
allocate — its success depends only on its own quota, never on other subjects' usage. -/
theorem availability_guarantee (reserved : Subject → ℕ) (s : Subject) (st : State)
    (hhead : used st s < reserved s) :
    used (alloc reserved s st) s = used st s + 1 := by
  have hlt : st s < reserved s := hhead
  show (if s = s ∧ st s < reserved s then st s + 1 else st s) = st s + 1
  rw [if_pos ⟨rfl, hlt⟩]

/-- **No cross-subject denial of service.** An allocation performed by a *different*
subject `s'` never changes `s`'s usage — hence never consumes `s`'s reserved
availability or reduces its headroom. -/
theorem no_cross_subject_dos (reserved : Subject → ℕ) (s s' : Subject) (st : State)
    (hne : s ≠ s') :
    used (alloc reserved s' st) s = used st s := by
  show (if s = s' ∧ st s' < reserved s' then st s + 1 else st s) = st s
  rw [if_neg (fun h => hne h.1)]

/-! ## Guaranteed progress (bounded liveness) -/

/-- From any state, replaying `k` allocations for `s` while `s` stays within its
reservation drives `s`'s usage up by exactly `k`. -/
theorem alloc_run_from (reserved : Subject → ℕ) (s : Subject) :
    ∀ (k : ℕ) (st : State), st s + k ≤ reserved s →
      run reserved (List.replicate k (Op.alloc s)) st s = st s + k := by
  intro k
  induction k with
  | zero =>
    intro st _
    show run reserved [] st s = st s + 0
    rfl
  | succ n ih =>
    intro st h
    rw [List.replicate_succ]
    show run reserved (List.replicate n (Op.alloc s)) (step reserved st (Op.alloc s)) s
        = st s + (n + 1)
    have hlt : st s < reserved s := by omega
    have hstep_s : (step reserved st (Op.alloc s)) s = st s + 1 := by
      show (if s = s ∧ st s < reserved s then st s + 1 else st s) = st s + 1
      rw [if_pos ⟨rfl, hlt⟩]
    have hbound : (step reserved st (Op.alloc s)) s + n ≤ reserved s := by
      rw [hstep_s]; omega
    have hrec := ih (step reserved st (Op.alloc s)) hbound
    rw [hrec, hstep_s]
    omega

/-- **Guaranteed progress.** Starting from the empty state, a subject can allocate up to
its full reservation: `k` allocations (for any `k ≤ reserved s`) drive its usage to `k`. -/
theorem can_reach_reservation (reserved : Subject → ℕ) (s : Subject) :
    ∀ k ≤ reserved s,
      run reserved (List.replicate k (Op.alloc s)) (fun _ => 0) s = k := by
  intro k hk
  have h := alloc_run_from reserved s k (fun _ => 0) (by simpa using hk)
  simpa using h

/-! ## Non-vacuity — a concrete, non-oversubscribed reservation table (`decide`-checked)

Subject `0` is guaranteed `3`, subject `1` guaranteed `2`, pool capacity `5`. -/

/-- reserved: `0 ↦ 3`, `1 ↦ 2`, everyone else `↦ 0`. -/
def reservedEx : Subject → ℕ := fun s => if s = 0 then 3 else if s = 1 then 2 else 0

/-- The two guaranteed subjects. -/
def Sex : Finset Subject := {0, 1}

/-- Non-oversubscription holds: `3 + 2 = 5 ≤ 5`. -/
example : (∑ s ∈ Sex, reservedEx s) ≤ 5 := by decide

/-- (a) Subject 0 reaches its full reservation of 3 **regardless of** subject 1's
interleaved allocations. -/
example :
    run reservedEx
      [Op.alloc 0, Op.alloc 1, Op.alloc 0, Op.alloc 1, Op.alloc 0]
      (fun _ => 0) 0 = 3 := by decide

/-- (b) An over-quota allocation is a **no-op** (fail-closed): subject 1's reservation is
2, so a third alloc does not raise its usage past 2. -/
example :
    run reservedEx [Op.alloc 1, Op.alloc 1, Op.alloc 1] (fun _ => 0) 1 = 2 := by decide

/-- (c) Subject 1's allocations **never reduce subject 0's headroom**: after subject 1 is
active, subject 0's usage is still 0, so its full reservation of 3 remains available. -/
example :
    run reservedEx [Op.alloc 1, Op.alloc 1] (fun _ => 0) 0 = 0 := by decide

end Brockian.HighAssurance.Availability
