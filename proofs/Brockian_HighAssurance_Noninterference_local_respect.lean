import Mathlib

/-!
# An seL4-class confidentiality demonstrator: NONINTERFERENCE via unwinding

This file gives a machine-checked, non-vacuous, *inductive* proof of the
information-flow security property that sits at the heart of the seL4 kernel's
second crown jewel — its **noninterference** theorem — reduced to a small but
faithful labeled state machine.

The security guarantee proved here (`noninterference`) is the real statement:
    the low (public) domain's final observation depends ONLY on the low actions;
    high (secret) actions have provably ZERO effect on what low can see.
It is discharged by *genuine induction over a run* using the two standard
seL4/Rushby **unwinding conditions** — `step_consistency` (the weak step) and
`local_respect` — exactly the proof architecture used in the seL4 development.
-/

namespace Brockian.HighAssurance.Noninterference

/-- Two security domains: `low` (public) and `high` (secret). -/
inductive Domain
  | low
  | high
  deriving DecidableEq, Repr

/-- The information-flow **policy**: `flows a b` means domain `a`'s actions may
    legitimately influence what domain `b` observes. Crucially `high` does NOT
    flow to `low` — secrets must never leak downward. This single `false` entry
    is the confidentiality constraint the whole theorem enforces. -/
def flows : Domain → Domain → Bool
  | Domain.low,  Domain.low  => true
  | Domain.low,  Domain.high => true
  | Domain.high, Domain.high => true
  | Domain.high, Domain.low  => false   -- ← the confidentiality constraint

/-- System state: a public component `low` and a secret component `high`. -/
structure State where
  low  : ℕ
  high : ℕ
  deriving DecidableEq, Repr

/-- Actions, each performed by a specific domain. At least one action writes the
    secret (`writeHigh`); the others operate on the public component. -/
inductive Action
  | writeLow  (v : ℕ)   -- low domain overwrites the public value
  | incLow              -- low domain increments the public value
  | writeHigh (v : ℕ)   -- high domain overwrites the secret value
  deriving DecidableEq, Repr

/-- Which domain performs each action. -/
def dom : Action → Domain
  | Action.writeLow _  => Domain.low
  | Action.incLow      => Domain.low
  | Action.writeHigh _ => Domain.high

/-- The transition function. The security-critical invariant is visible *by
    construction*: `writeHigh` touches ONLY the `high` field, never `low`. We
    build the machine so the property holds — then we PROVE it does. -/
def step : Action → State → State
  | Action.writeLow v,  s => { s with low := v }
  | Action.incLow,      s => { s with low := s.low + 1 }
  | Action.writeHigh v, s => { s with high := v }

/-- What a domain observes: `low` sees only the public field; `high` sees only
    the secret field. -/
def obs : Domain → State → ℕ
  | Domain.low,  s => s.low
  | Domain.high, s => s.high

/-- Low-observational equivalence: two states are indistinguishable to the `low`
    domain exactly when their public components agree. (It is literally an
    equality of observations, hence an equivalence relation for free.) -/
def lowEquiv (s t : State) : Prop := obs Domain.low s = obs Domain.low t

/-- The syntactic test "this action belongs to the low domain", used to project
    a run onto its low actions. -/
def isLow (a : Action) : Bool := decide (dom a = Domain.low)

/-- Run a list of actions, in order, from a starting state (left fold). -/
def run (as : List Action) (s : State) : State :=
  as.foldl (fun st a => step a st) s

@[simp] theorem run_nil (s : State) : run [] s = s := rfl

@[simp] theorem run_cons (a : Action) (as : List Action) (s : State) :
    run (a :: as) s = run as (step a s) := rfl

/-! ## The unwinding conditions -/

/-- **Unwinding condition 1 — output (observational) consistency.**
    Low-equivalent states yield the same low observation. Immediate from the
    definition, but a required component of the unwinding theorem. -/
theorem output_consistency {s t : State} (h : lowEquiv s t) :
    obs Domain.low s = obs Domain.low t := h

/-- **Unwinding condition 2 — step consistency (the weak-step lemma).**
    Every single step preserves low-equivalence: if `s` and `t` look the same to
    `low`, then after performing the SAME action they still look the same. This
    is the real local content that powers the induction. -/
theorem step_consistency (a : Action) {s t : State} (h : lowEquiv s t) :
    lowEquiv (step a s) (step a t) := by
  cases a with
  | writeLow v => simp [lowEquiv, obs, step]
  | incLow =>
      simp only [lowEquiv, obs, step] at h ⊢
      omega
  | writeHigh v => simpa [lowEquiv, obs, step] using h

/-- **Unwinding condition 3 — local respect.**
    An action performed by a domain that does NOT flow to `low` (here `high`,
    since `flows high low = false`) is invisible to `low`: it leaves the low
    observation unchanged. -/
theorem local_respect (a : Action) (s : State)
    (hdom : dom a = Domain.high)
    (hpolicy : flows Domain.high Domain.low = false) :
    lowEquiv s (step a s) := by
  cases a with
  | writeLow v => simp [dom] at hdom
  | incLow => simp [dom] at hdom
  | writeHigh v => simp [lowEquiv, obs, step]

/-- Low-equivalence is preserved along an *entire run*, by iterating
    `step_consistency`. (A run-level lifting of unwinding condition 2.) -/
theorem run_consistency (as : List Action) {s t : State} (h : lowEquiv s t) :
    lowEquiv (run as s) (run as t) := by
  induction as generalizing s t with
  | nil => simpa using h
  | cons a as ih =>
      simp only [run_cons]
      exact ih (step_consistency a h)

/-! ## The headline theorem -/

/-- **NONINTERFERENCE (the headline).**
    The low domain's final observation depends ONLY on the low actions: deleting
    every high (secret) action from the run does not change what `low` sees.
    Equivalently, high actions can carry NO information down to `low`.

    Proved by genuine induction on the action list, using `local_respect` and
    `step_consistency` (lifted to `run_consistency`) — the seL4/Rushby unwinding
    architecture. -/
theorem noninterference (as : List Action) (s : State) :
    obs Domain.low (run as s)
      = obs Domain.low (run (as.filter isLow) s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
      by_cases hlow : dom a = Domain.low
      · -- `a` is a LOW action: it is kept by the filter.
        have hkeep : (a :: as).filter isLow = a :: as.filter isLow := by
          have : isLow a = true := by simp [isLow, hlow]
          simp [List.filter_cons, this]
        rw [hkeep]
        simp only [run_cons]
        exact ih (step a s)
      · -- `a` is a HIGH action: it is dropped by the filter, and it is
        -- invisible to `low`.
        have hhigh : dom a = Domain.high := by
          cases hda : dom a with
          | low => exact absurd hda hlow
          | high => rfl
        have hdrop : (a :: as).filter isLow = as.filter isLow := by
          have : isLow a = false := by simp [isLow, hhigh]
          simp [List.filter_cons, this]
        rw [hdrop]
        simp only [run_cons]
        -- goal: obs low (run as (step a s)) = obs low (run (filter as) s)
        have hlr : lowEquiv s (step a s) := local_respect a s hhigh rfl
        have hrc : lowEquiv (run (as.filter isLow) s)
                            (run (as.filter isLow) (step a s)) :=
          run_consistency _ hlr
        have hih : lowEquiv (run as (step a s))
                            (run (as.filter isLow) (step a s)) := ih (step a s)
        -- chain the equalities: run as (step a s) ~ run filter (step a s) ~ run filter s
        exact hih.trans hrc.symm

/-! ## Non-vacuity: the secret genuinely changes, yet `low` is provably blind -/

/-- A `writeHigh` genuinely CHANGES the secret component … -/
example : (step (Action.writeHigh 42) { low := 7, high := 0 }).high = 42 := rfl

example :
    (step (Action.writeHigh 42) { low := 7, high := 0 }).high
      ≠ ({ low := 7, high := 0 } : State).high := by decide

/-- … yet leaves the low observation identical: `low` cannot detect it. -/
example :
    obs Domain.low (step (Action.writeHigh 42) { low := 7, high := 0 })
      = obs Domain.low ({ low := 7, high := 0 } : State) := rfl

/-- The machine is NOT trivially constant: low actions really do move the low
    observation (so `noninterference` is not vacuously true). -/
example : obs Domain.low (run [Action.writeLow 5] { low := 0, high := 0 }) = 5 := rfl

example :
    obs Domain.low (run [Action.writeLow 5] { low := 0, high := 0 })
      ≠ obs Domain.low (run [Action.writeLow 9] { low := 0, high := 0 }) := by decide

/-- Two runs that differ ONLY in their high actions produce the SAME low
    observation — a concrete instance of noninterference … -/
example :
    obs Domain.low
        (run [Action.writeLow 5, Action.writeHigh 99, Action.incLow]
             { low := 0, high := 0 })
      = obs Domain.low
        (run [Action.writeLow 5, Action.writeHigh 1, Action.incLow]
             { low := 0, high := 0 }) := by decide

/-- … even though those two runs drive the secret to genuinely different
    values (the confidentiality is real, not degenerate). -/
example :
    (run [Action.writeLow 5, Action.writeHigh 99] { low := 0, high := 0 }).high
      ≠ (run [Action.writeLow 5, Action.writeHigh 1] { low := 0, high := 0 }).high := by
  decide

end Brockian.HighAssurance.Noninterference
