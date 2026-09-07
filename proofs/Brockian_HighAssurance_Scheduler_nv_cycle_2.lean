import Mathlib

/-!
# Capability-Microkernel Scheduler Correctness (round-robin dispatch)

A capability microkernel time-multiplexes a set of *threads* over the CPU through a
**scheduler**.  Threads sit in a *ready queue*; on each dispatch the kernel selects one
of them to become the `current` (running) thread.  Two properties must hold for the
scheduler to be trustworthy:

* **Safety** — the scheduler *never runs a thread it is not allowed to run*.  Only a
  `runnable` thread (one that is not blocked / not descheduled by policy) may ever be
  `current`.  This is a kernel *integrity* invariant: it must be preserved by every
  dispatch and hence across an arbitrary execution.

* **Progress / fairness (no starvation)** — round-robin dispatch is *fair*: every thread
  sitting in the ready queue is eventually dispatched.  Concretely, a thread at position
  `k` of a ready queue of runnable threads becomes `current` within one queue cycle
  (`k+1 ≤ |ready|` steps).  No thread waits forever behind the others.

* **Work-conserving** — the CPU is never left idle while a runnable thread waits: if the
  ready queue contains a runnable thread, the next dispatch picks someone.

We model a **round-robin scheduler with skip**: `schedStep` dispatches the *first
runnable* thread in the ready queue (skipping blocked / non-runnable threads in the same
step) and rotates the queue by one so the next cycle advances.  `runnable : Thread → Prop`
is the *static* (decidable) runnability classification of the kernel.

This is the scheduler-integrity + fairness guarantee of a capability microkernel.
-/

namespace Brockian.HighAssurance.Scheduler

/-- Threads are identified by natural numbers (thread control block ids). -/
abbrev Thread := ℕ

/-- Scheduler state: the FIFO `ready` queue and the currently-running thread (if any). -/
structure SchedState where
  /-- The ready queue (round-robin order). -/
  ready : List Thread
  /-- The thread the CPU is currently executing, if any. -/
  current : Option Thread

section Model

-- The kernel's *static* runnability policy: `runnable t` holds iff thread `t` is
-- eligible to run (not blocked, not administratively descheduled).  Decidable, since
-- the kernel must be able to test it at dispatch time.
variable (runnable : Thread → Prop) [∀ t, Decidable (runnable t)]

/-- Select the **first runnable** thread of a queue, skipping non-runnable (blocked)
    threads.  Returns `none` on a queue with no runnable thread. -/
def firstRunnable : List Thread → Option Thread
  | []        => none
  | h :: rest => if runnable h then some h else firstRunnable rest

/-- Rotate the queue by one position (round-robin advance): the head goes to the back. -/
def rotate : List Thread → List Thread
  | []        => []
  | h :: rest => rest ++ [h]

/-- **One dispatch step.**  `current` becomes the first runnable thread of the ready
    queue (blocked threads are skipped, *never* dispatched); the queue rotates by one so
    the next dispatch advances round-robin. -/
def schedStep (s : SchedState) : SchedState :=
  { current := firstRunnable runnable s.ready, ready := rotate s.ready }

/-- Iterate the scheduler `n` dispatch steps. -/
def run : ℕ → SchedState → SchedState
  | 0,     s => s
  | n + 1, s => run n (schedStep runnable s)

/-- **The scheduler safety invariant:** the running thread is always runnable. -/
def SchedInv (s : SchedState) : Prop := ∀ t, s.current = some t → runnable t

/-! ### Definitional rewrite lemmas -/

@[simp] theorem firstRunnable_nil : firstRunnable runnable ([] : List Thread) = none := rfl

@[simp] theorem firstRunnable_cons (h : Thread) (rest : List Thread) :
    firstRunnable runnable (h :: rest)
      = if runnable h then some h else firstRunnable runnable rest := rfl

@[simp] theorem rotate_nil : rotate ([] : List Thread) = [] := rfl

@[simp] theorem rotate_cons (h : Thread) (rest : List Thread) :
    rotate (h :: rest) = rest ++ [h] := rfl

@[simp] theorem schedStep_current (s : SchedState) :
    (schedStep runnable s).current = firstRunnable runnable s.ready := rfl

@[simp] theorem schedStep_ready (s : SchedState) :
    (schedStep runnable s).ready = rotate s.ready := rfl

@[simp] theorem run_zero (s : SchedState) : run runnable 0 s = s := rfl

@[simp] theorem run_succ (n : ℕ) (s : SchedState) :
    run runnable (n + 1) s = run runnable n (schedStep runnable s) := rfl

/-! ## Safety — the scheduler never runs a non-runnable thread -/

/-- `firstRunnable` only ever returns a *runnable* thread. -/
theorem firstRunnable_spec :
    ∀ (l : List Thread) (t : Thread), firstRunnable runnable l = some t → runnable t := by
  intro l
  induction l with
  | nil => intro t h; rw [firstRunnable_nil] at h; simp at h
  | cons hd tl ih =>
      intro t h
      rw [firstRunnable_cons] at h
      by_cases hr : runnable hd
      · rw [if_pos hr] at h
        have he : hd = t := Option.some.inj h
        exact he ▸ hr
      · rw [if_neg hr] at h
        exact ih t h

/-- **Scheduler safety (one step).**  A single dispatch preserves the invariant: the
    thread it makes `current` is runnable.  (The invariant `hinv` on the prior state is
    not even needed — `schedStep` *establishes* the invariant unconditionally.) -/
theorem sched_safety (s : SchedState) (hinv : SchedInv runnable s) :
    SchedInv runnable (schedStep runnable s) := by
  intro t ht
  rw [schedStep_current] at ht
  exact firstRunnable_spec runnable s.ready t ht

/-- **Scheduler safety (lifted to arbitrary runs).**  If the initial state satisfies the
    invariant, then so does the state after *any* number `n` of dispatch steps.  No
    reachable state ever runs a non-runnable thread. -/
theorem sched_safety_run (n : ℕ) (s : SchedState) (hinv : SchedInv runnable s) :
    SchedInv runnable (run runnable n s) := by
  induction n generalizing s with
  | zero => rw [run_zero]; exact hinv
  | succ n ih => rw [run_succ]; exact ih (schedStep runnable s) (sched_safety runnable s hinv)

/-- Any state whose CPU is idle (`current = none`) trivially satisfies the invariant —
    a convenient way to start a run. -/
theorem schedInv_of_current_none (s : SchedState) (h : s.current = none) :
    SchedInv runnable s := by
  intro t ht; rw [h] at ht; simp at ht

/-- **Corollary — a blocked thread is never dispatched.**  If `t` is not runnable, then
    starting from any invariant-satisfying state, `t` is *never* the `current` thread,
    at any step `n`.  Blocked threads are permanently skipped. -/
theorem nonrunnable_never_current (n : ℕ) (s : SchedState) (hinv : SchedInv runnable s)
    (t : Thread) (hnr : ¬ runnable t) : (run runnable n s).current ≠ some t := by
  intro hc
  exact hnr (sched_safety_run runnable n s hinv t hc)

/-! ## Work-conserving — a nonempty runnable queue always dispatches someone -/

/-- If a queue contains at least one runnable thread, `firstRunnable` finds one. -/
theorem firstRunnable_isSome :
    ∀ (l : List Thread), (∃ t ∈ l, runnable t) → firstRunnable runnable l ≠ none := by
  intro l
  induction l with
  | nil => rintro ⟨t, ht, _⟩; simp at ht
  | cons hd tl ih =>
      rintro ⟨t, ht, hr⟩
      rw [firstRunnable_cons]
      by_cases hh : runnable hd
      · rw [if_pos hh]; exact Option.some_ne_none hd
      · rw [if_neg hh]
        apply ih
        rcases List.mem_cons.mp ht with heq | hmem
        · exact absurd (heq ▸ hr) hh
        · exact ⟨t, hmem, hr⟩


/-- **Work-conserving.**  If the ready queue holds a runnable thread, the scheduler does
    not idle: after a dispatch step, `current` is populated. -/
theorem work_conserving (s : SchedState) (hne : ∃ t ∈ s.ready, runnable t) :
    (schedStep runnable s).current ≠ none := by
  rw [schedStep_current]
  exact firstRunnable_isSome runnable s.ready hne

/-! ## No starvation (round-robin fairness / progress) -/

/-- **Progress kernel.**  In a ready queue of runnable threads, the thread at index `k`
    is dispatched at step `k+1`.  Proved by induction on the queue position `k`: each
    step rotates the head to the back, sliding position `k+1` down to position `k`. -/
theorem progress :
    ∀ (k : ℕ) (s : SchedState), (∀ x ∈ s.ready, runnable x) →
      ∀ t, s.ready[k]? = some t → (run runnable (k + 1) s).current = some t := by
  intro k
  induction k with
  | zero =>
      intro s hall t hget
      cases hs : s.ready with
      | nil => rw [hs, List.getElem?_nil] at hget; simp at hget
      | cons h rest =>
          rw [hs, List.getElem?_cons_zero] at hget
          have hht : h = t := Option.some.inj hget
          have hrh : runnable h := hall h (by rw [hs]; exact List.mem_cons.mpr (Or.inl rfl))
          rw [run_succ, run_zero, schedStep_current, hs, firstRunnable_cons, if_pos hrh, hht]
  | succ k ih =>
      intro s hall t hget
      cases hs : s.ready with
      | nil => rw [hs, List.getElem?_nil] at hget; simp at hget
      | cons h rest =>
          rw [hs, List.getElem?_cons_succ] at hget
          -- `hget : rest[k]? = some t`
          have hlt : k < rest.length := by
            rcases Nat.lt_or_ge k rest.length with hk | hk
            · exact hk
            · rw [List.getElem?_eq_none hk] at hget; simp at hget
          have hall' : ∀ x ∈ (schedStep runnable s).ready, runnable x := by
            intro x hx
            rw [schedStep_ready, hs, rotate_cons, List.mem_append] at hx
            rcases hx with hxr | hxh
            · exact hall x (by rw [hs]; exact List.mem_cons.mpr (Or.inr hxr))
            · rw [List.mem_singleton] at hxh
              exact hall x (by rw [hs, hxh]; exact List.mem_cons.mpr (Or.inl rfl))
          have hget' : (schedStep runnable s).ready[k]? = some t := by
            rw [schedStep_ready, hs, rotate_cons, List.getElem?_append_left hlt]
            exact hget
          rw [run_succ]
          exact ih (schedStep runnable s) hall' t hget'

/-- **No starvation (round-robin fairness).**  Every thread in a ready queue of runnable
    threads is dispatched within one queue cycle: if `t ∈ ready`, there is a step count
    `n ≤ |ready|` at which `t` becomes the `current` running thread. -/
theorem no_starvation (s : SchedState) (t : Thread) (hin : t ∈ s.ready)
    (hall : ∀ x ∈ s.ready, runnable x) :
    ∃ n, n ≤ s.ready.length ∧ (run runnable n s).current = some t := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hin
  refine ⟨k + 1, by omega, ?_⟩
  apply progress runnable k s hall t
  rw [List.getElem?_eq_getElem hk, hget]

end Model

/-! ## Non-vacuity — a concrete scheduler instance (`decide`-checked)

Threads `1, 2, 3` are runnable; thread `4` is *blocked* (non-runnable).  We exhibit the
round-robin cycle, the fairness bound, and the skip-the-blocked-thread behaviour by kernel
computation. -/

section Concrete

/-- Concrete runnability policy: threads 1, 2, 3 are runnable; everything else (e.g. the
    blocked thread 4) is not.  `abbrev` so its `Decidable` instance reduces for `decide`. -/
abbrev crun (t : Thread) : Prop := t = 1 ∨ t = 2 ∨ t = 3

/-- Initial state: ready queue `[1,2,3]`, CPU idle. -/
def s0 : SchedState := { ready := [1, 2, 3], current := none }

/-- State with a *blocked* thread `4` at the head of the queue. -/
def sBlk : SchedState := { ready := [4, 1, 2, 3], current := none }

/-! ### (a) Round-robin cycles 1 → 2 → 3 → 1 -/

theorem nv_cycle_1 : (run crun 1 s0).current = some 1 := by decide
theorem nv_cycle_2 : (run crun 2 s0).current = some 2 := by decide
theorem nv_cycle_3 : (run crun 3 s0).current = some 3 := by decide
/-- After a full cycle of length 3 the schedule wraps back to thread 1. -/
theorem nv_cycle_wrap : (run crun 4 s0).current = some 1 := by decide

/-! ### (b) Every ready thread is dispatched within one cycle (3 steps) -/

theorem nv_starve_1 : ∃ n ≤ 3, (run crun n s0).current = some 1 := ⟨1, by decide, by decide⟩
theorem nv_starve_2 : ∃ n ≤ 3, (run crun n s0).current = some 2 := ⟨2, by decide, by decide⟩
theorem nv_starve_3 : ∃ n ≤ 3, (run crun n s0).current = some 3 := ⟨3, by decide, by decide⟩

/-- The general `no_starvation` theorem instantiated on the concrete queue: every thread
    of `[1,2,3]` is guaranteed dispatched within `|ready| = 3` steps. -/
theorem nv_no_starvation_general (t : Thread) (hin : t ∈ s0.ready) :
    ∃ n, n ≤ s0.ready.length ∧ (run crun n s0).current = some t :=
  no_starvation crun s0 t hin (by decide)

/-! ### (c) A blocked / non-runnable thread is skipped, never dispatched -/

/-- One step from `[4,1,2,3]`: the blocked thread 4 at the head is *skipped* and thread 1
    runs instead. -/
theorem nv_blocked_skipped : (schedStep crun sBlk).current = some 1 := by decide

/-- Thread 4, being non-runnable, is **never** dispatched — at *any* step `n` (a
    consequence of the general safety invariant, not a finite check). -/
theorem nv_blocked_never_current (n : ℕ) : (run crun n sBlk).current ≠ some 4 :=
  nonrunnable_never_current crun n sBlk (schedInv_of_current_none crun sBlk rfl) 4 (by decide)

end Concrete

end Brockian.HighAssurance.Scheduler
