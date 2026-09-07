import Mathlib

/-!
# Controlled declassification: noninterference WITH a trusted downgrade channel

Pure noninterference (see `HighAssuranceNoninterference.lean`) forbids ALL high→low
flow. That is too strong for real systems: a login check must reveal at least one bit
of the secret (accept / reject), an aggregate must reveal a statistic, an encryptor
must release ciphertext. **Controlled declassification** is the realistic model: it
permits high→low flow ONLY through an explicit, auditable `declassify` action, and
proves that Low learns *nothing about High beyond what was explicitly declassified*.

The security policy is fixed by a **release function** `f : ℕ → ℕ`: the declassify
action is the sole sanctioned channel and it releases exactly `f high` (e.g.
`f = (· % 2)` releases one bit — the login-check bit). Everything else about the
secret is provably invisible to Low.

We prove, by genuine induction over a run:

* `high_write_no_low_effect`      — a secret write never moves Low's view (unwinding).
* `step_low_consistency`          — a non-declassify step preserves Low-equivalence
                                    (the weak-step / Rushby unwinding condition).
* `run_low_consistency`           — that condition lifted along an entire run.
* `high_write_not_declassified_invisible` — a secret write that is NEVER subsequently
                                    declassified leaves Low's view unchanged (the
                                    honest "filter" statement: unreleased secret
                                    activity leaks nothing).
* `delimited_release`  (HEADLINE) — any two states agreeing on Low AND on the released
                                    quantity `f high` are Low-indistinguishable forever,
                                    even across declassifications. Low learns EXACTLY
                                    `f high`, never more. (Sabelfeld–Sands delimited
                                    release / relaxed noninterference.)
* `no_declassify_noninterference` (SPECIAL CASE) — with no declassify action, Low is
                                    independent of High regardless of `f` — i.e. pure
                                    noninterference is recovered.
* `controlled_release_no_declassify` — the pure-NI theorem in Rushby's `filter` form.

Non-vacuity witnesses close the file: a secret write is Low-invisible; the sanctioned
channel genuinely moves Low's view and releases precisely `f high`; yet two secrets with
the same `f`-image remain indistinguishable even after declassification.
-/

namespace Brockian.HighAssurance.Declassification

/-- System state: a public component `low`, a secret component `high`, and an
    append-only `released` audit log recording every declassified value. Low observes
    `low` and `released`; `high` is the secret. -/
structure State where
  low      : ℕ
  high     : ℕ
  released : List ℕ
  deriving DecidableEq, Repr

/-- Actions. `writeLow`/`compute` are public operations on the low component;
    `writeHigh` writes the secret; `declassify` is the ONLY sanctioned high→low
    channel — it copies the designated release value `f high` into `low` and appends it
    to the audit log. -/
inductive Action
  | writeLow  (v : ℕ)   -- public: overwrite the public value
  | compute             -- public op on the public value (models a low computation)
  | writeHigh (v : ℕ)   -- secret: overwrite the secret value
  | declassify          -- sanctioned downgrade: release `f high` to low + audit log
  deriving DecidableEq, Repr

/-- Syntactic test: "this action is a purely public (low) operation". -/
def isLow : Action → Bool
  | Action.writeLow _  => true
  | Action.compute     => true
  | Action.writeHigh _ => false
  | Action.declassify  => false

/-- Syntactic test: "this action is the sanctioned declassify channel". -/
def isDeclassify : Action → Bool
  | Action.declassify => true
  | _                 => false

/-- What Low observes: the public value together with the auditable release log.
    (Not the secret `high`.) -/
def lowObs (s : State) : ℕ × List ℕ := (s.low, s.released)

section
/-! The release policy `f : ℕ → ℕ` is the fixed function of `high` that the sanctioned
    channel is permitted to leak to Low. `f = (· % 2)` releases one bit (a login check);
    a constant `f` releases nothing; `f = id` fully declassifies. -/
variable (f : ℕ → ℕ)

/-- The transition function. Only `declassify` reads `high`, and it releases exactly
    `f high` — the single sanctioned high→low flow, made explicit and audited. -/
def step : Action → State → State
  | Action.writeLow v,  s => { s with low := v }
  | Action.compute,     s => { s with low := s.low + 1 }
  | Action.writeHigh v, s => { s with high := v }
  | Action.declassify,  s => { s with low := f s.high, released := f s.high :: s.released }

/-- Run a list of actions, in order, from a starting state (left fold). -/
def run (as : List Action) (s : State) : State :=
  as.foldl (fun st a => step f a st) s

@[simp] theorem run_nil (s : State) : run f [] s = s := rfl

@[simp] theorem run_cons (a : Action) (as : List Action) (s : State) :
    run f (a :: as) s = run f as (step f a s) := rfl

@[simp] theorem run_append (as bs : List Action) (s : State) :
    run f (as ++ bs) s = run f bs (run f as s) := by
  simp [run, List.foldl_append]

/-! ## Unwinding lemmas -/

/-- **Local respect (unwinding condition).** A secret write is invisible to Low: it
    leaves the low observation completely unchanged. -/
theorem high_write_no_low_effect (v : ℕ) (s : State) :
    lowObs (step f (Action.writeHigh v) s) = lowObs s := rfl

/-- **Step consistency (the weak-step lemma / unwinding condition).** Every
    *non-declassify* step preserves Low-equivalence: two states with the same low
    observation still have the same low observation after the SAME non-declassify
    action. (Non-declassify actions compute the public component from the public
    component alone, never from the secret.) -/
theorem step_low_consistency (a : Action) {s t : State}
    (h : lowObs s = lowObs t) (hnd : isDeclassify a = false) :
    lowObs (step f a s) = lowObs (step f a t) := by
  have hlow : s.low = t.low := by
    simpa [lowObs] using congrArg Prod.fst h
  have hrel : s.released = t.released := by
    simpa [lowObs] using congrArg Prod.snd h
  cases a with
  | writeLow v => simp [step, lowObs, hrel]
  | compute    => simp [step, lowObs, hlow, hrel]
  | writeHigh v => simpa [step, lowObs] using h
  | declassify => simp [isDeclassify] at hnd

/-- Low-equivalence is preserved along an entire *declassify-free* run, by iterating
    `step_low_consistency`. -/
theorem run_low_consistency :
    ∀ (as : List Action), (∀ a ∈ as, isDeclassify a = false) →
      ∀ {s t : State}, lowObs s = lowObs t →
        lowObs (run f as s) = lowObs (run f as t) := by
  intro as
  induction as with
  | nil => intro _ s t h; simpa using h
  | cons a as ih =>
      intro hnd s t h
      simp only [run_cons]
      exact ih (fun b hb => hnd b (by simp [hb]))
        (step_low_consistency f a h (hnd a (by simp)))

/-- **A secret write that is never subsequently declassified is invisible to Low.**
    This is the honest single-run "filter" statement: unreleased secret activity leaks
    nothing. (The naive filter that drops *all* high writes is FALSE — a write that is
    later declassified genuinely changes the released value; here `bs` is required to
    contain no declassify, i.e. the write is never released.) -/
theorem high_write_not_declassified_invisible
    (as bs : List Action) (v : ℕ) (s : State)
    (hbs : ∀ a ∈ bs, isDeclassify a = false) :
    lowObs (run f (as ++ Action.writeHigh v :: bs) s)
      = lowObs (run f (as ++ bs) s) := by
  rw [run_append, run_append]
  simp only [run_cons]
  exact run_low_consistency f bs hbs (high_write_no_low_effect f v (run f as s))

/-! ## The headline: delimited release -/

/-- Invariant preserved by a single step of ANY action, given that two states agree on
    Low and on the released quantity `f high`: they continue to agree on low, on
    `f high`, and on the audit log. This is the heart of delimited release — including
    the `declassify` case, where both states release the SAME value because they agree
    on `f high`. -/
theorem step_delim (a : Action) {s t : State}
    (h : s.low = t.low ∧ f s.high = f t.high ∧ s.released = t.released) :
    (step f a s).low = (step f a t).low ∧
      f (step f a s).high = f (step f a t).high ∧
      (step f a s).released = (step f a t).released := by
  obtain ⟨hlow, hf, hrel⟩ := h
  cases a with
  | writeLow v  => exact ⟨rfl, hf, hrel⟩
  | compute     => exact ⟨by simp [step, hlow], hf, hrel⟩
  | writeHigh v => exact ⟨hlow, rfl, hrel⟩
  | declassify  => exact ⟨hf, hf, by simp [step, hf, hrel]⟩

/-- The invariant of `step_delim` lifted along an entire run (all actions, including
    declassify). -/
theorem run_delim :
    ∀ (as : List Action) {s t : State},
      (s.low = t.low ∧ f s.high = f t.high ∧ s.released = t.released) →
        (run f as s).low = (run f as t).low ∧
          f (run f as s).high = f (run f as t).high ∧
          (run f as s).released = (run f as t).released := by
  intro as
  induction as with
  | nil => intro s t h; simpa using h
  | cons a as ih =>
      intro s t h
      simp only [run_cons]
      exact ih (step_delim f a h)

/-- **DELIMITED RELEASE (the headline).** Any two states that agree on the low
    component AND on the released quantity `f high` (and on the audit log) are
    indistinguishable to Low across ANY run — even one containing declassifications.

    Read as a confidentiality guarantee: Low learns EXACTLY `f high` about the secret,
    and nothing more. Everything about `high` beyond its `f`-image is provably hidden,
    while the sanctioned channel still delivers `f high`. This is the realistic
    replacement for pure noninterference (which is the special case `f` constant /
    no declassify). Proved by induction on the run via the `run_delim` invariant. -/
theorem delimited_release (as : List Action) {s t : State}
    (hlow : s.low = t.low) (hf : f s.high = f t.high)
    (hlog : s.released = t.released) :
    lowObs (run f as s) = lowObs (run f as t) := by
  obtain ⟨h1, _, h3⟩ := run_delim f as ⟨hlow, hf, hlog⟩
  simp only [lowObs, h1, h3]

/-! ## Special case: pure noninterference recovered (no declassification) -/

/-- **PURE NONINTERFERENCE (special case).** With NO declassify action in the run, Low
    is fully independent of High: two states agreeing on the low component (and audit
    log) are Low-indistinguishable regardless of their secrets — no hypothesis on `f`
    or on `high` is needed. Absent the sanctioned channel, controlled declassification
    collapses to the standard noninterference theorem. -/
theorem no_declassify_noninterference (as : List Action) {s t : State}
    (hlow : s.low = t.low) (hlog : s.released = t.released)
    (hnd : ∀ a ∈ as, isDeclassify a = false) :
    lowObs (run f as s) = lowObs (run f as t) :=
  run_low_consistency f as hnd (by simp only [lowObs, hlow, hlog])

/-- The pure-NI theorem in Rushby's projection (`filter`) form: with no declassify
    action, Low's view depends only on the low actions — every secret write can be
    deleted from the run without changing what Low sees. -/
theorem controlled_release_no_declassify (as : List Action)
    (hnd : ∀ a ∈ as, isDeclassify a = false) (s : State) :
    lowObs (run f as s) = lowObs (run f (as.filter isLow) s) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
      have hnd' : ∀ b ∈ as, isDeclassify b = false :=
        fun b hb => hnd b (by simp [hb])
      by_cases hlow : isLow a = true
      · have hkeep : (a :: as).filter isLow = a :: as.filter isLow := by
          simp [List.filter_cons, hlow]
        rw [hkeep]; simp only [run_cons]
        exact ih hnd' (step f a s)
      · have hlowF : isLow a = false := by
          cases h : isLow a with
          | true => exact absurd h hlow
          | false => rfl
        have hdrop : (a :: as).filter isLow = as.filter isLow := by
          simp [List.filter_cons, hlowF]
        rw [hdrop]; simp only [run_cons]
        have hstep : lowObs (step f a s) = lowObs s := by
          cases a with
          | writeLow v  => simp [isLow] at hlowF
          | compute     => simp [isLow] at hlowF
          | writeHigh v => rfl
          | declassify  => have := hnd Action.declassify (by simp); simp [isDeclassify] at this
        have hndF : ∀ b ∈ as.filter isLow, isDeclassify b = false :=
          fun b hb => hnd' b (List.mem_of_mem_filter hb)
        calc lowObs (run f as (step f a s))
            = lowObs (run f (as.filter isLow) (step f a s)) := ih hnd' (step f a s)
          _ = lowObs (run f (as.filter isLow) s) :=
                run_low_consistency f (as.filter isLow) hndF hstep

end

/-! ## Non-vacuity: the model is real, and the leak is exactly the sanctioned one

Concrete release policy `f = (· % 2)` — declassify leaks exactly one bit of the secret
(the parity, e.g. a login accept/reject). -/

/-- The one-bit release policy. -/
def parity : ℕ → ℕ := fun h => h % 2

/-- The all-zero initial state. -/
def s0 : State := { low := 0, high := 0, released := [] }

/-! ### (a) A secret write changes the secret, yet Low is provably blind to it. -/

example : (step parity (Action.writeHigh 42) { low := 7, high := 0, released := [] }).high = 42 :=
  by decide
example :
    (step parity (Action.writeHigh 42) { low := 7, high := 0, released := [] }).high
      ≠ ({ low := 7, high := 0, released := [] } : State).high := by decide
/-- … but Low's observation is untouched (an instance of `high_write_no_low_effect`). -/
example :
    lowObs (step parity (Action.writeHigh 42) { low := 7, high := 0, released := [] })
      = lowObs ({ low := 7, high := 0, released := [] } : State) := rfl

/-! ### (b) Two runs differing ONLY in the secret (no declassify) look identical to Low
     — yet drive the secret to genuinely different values. -/

example :
    lowObs (run parity [Action.writeLow 5, Action.writeHigh 99, Action.compute] s0)
      = lowObs (run parity [Action.writeLow 5, Action.writeHigh 1, Action.compute] s0) := by
  decide
example :
    (run parity [Action.writeLow 5, Action.writeHigh 99, Action.compute] s0).high
      ≠ (run parity [Action.writeLow 5, Action.writeHigh 1, Action.compute] s0).high := by
  decide
/-- The machine is not trivially constant: low actions really move Low's view. -/
example : lowObs (run parity [Action.writeLow 5] s0) = (5, ([] : List ℕ)) := by decide
example :
    lowObs (run parity [Action.writeLow 5] s0)
      ≠ lowObs (run parity [Action.writeLow 9] s0) := by decide

/-! ### (c) The sanctioned channel WORKS: declassify moves Low's view and releases
     exactly `parity high` — so the theorem is not vacuous (the channel genuinely leaks
     the intended value, and only that). -/

/-- Declassify pushes exactly `parity high` to both the low value and the audit log. -/
example : (run parity [Action.writeHigh 7, Action.declassify] s0).low = 1 := by decide
example : (run parity [Action.writeHigh 7, Action.declassify] s0).released = [1] := by decide
/-- Two secrets with DIFFERENT parity are distinguished by Low through the channel —
    the leak is real. (So `delimited_release`'s `f`-agreement hypothesis is essential.) -/
example :
    lowObs (run parity [Action.writeHigh 7, Action.declassify] s0)
      ≠ lowObs (run parity [Action.writeHigh 8, Action.declassify] s0) := by decide

/-! ### (d) …yet Low learns ONLY `parity high`: two secrets with the SAME parity remain
     indistinguishable even AFTER a declassification — a live instance of the headline. -/

example :
    lowObs (run parity [Action.declassify, Action.writeLow 3] { low := 0, high := 4, released := [] })
      = lowObs (run parity [Action.declassify, Action.writeLow 3] { low := 0, high := 6, released := [] }) :=
  delimited_release parity _ rfl (by decide) rfl
/-- …even though those two states hold genuinely different secrets. -/
example : (4 : ℕ) ≠ 6 := by decide

end Brockian.HighAssurance.Declassification
