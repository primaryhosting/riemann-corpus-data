import Mathlib

/-!
# Constant-Time / Observation-Noninterference for a tiny instruction language

A computation is **constant-time** (leakage-free) if its OBSERVABLE TRACE — the
sequence of branch decisions plus accessed memory addresses, the classic
timing/cache side-channel model — depends ONLY on public inputs, never on secrets.

We model a tiny instruction language with a *leakage semantics* (`exec` emits a
trace of `Obs`), a structural predicate `ctProgram` characterising programs that use
only data-oblivious / public-address instructions, and prove:

* `ct_trace_noninterference` — for a `ctProgram`, two states agreeing on the public
  part (but with ARBITRARY secrets) produce the *same* trace.  This is exactly the
  definition of "no timing/cache side channel".
* `leaky_program_leaks` — a program using `branchOnSecret` whose trace DIFFERS for two
  states agreeing on the public part.  The `ct` restriction therefore has teeth: it is
  necessary, not vacuous.
* `condMove_correct` / `condMove_no_leak` — the data-oblivious select computes the same
  result value a secret branch would, while emitting an empty trace: constant-time
  discipline preserves functional correctness.

Everything is checked by AXLE (Lean 4.32.2 + Mathlib), axiom-clean, no `sorry`.
-/

namespace Brockian.HighAssurance.ConstantTime

/-- A value is a natural number. -/
abbrev Val := ℕ

/-- A machine state splits into a `pub`lic register and a `sec`ret register.
    An attacker may observe leakage derived from the state, but never the state itself. -/
structure State where
  pub : Val
  sec : Val
deriving DecidableEq, Repr

/-- A *public expression*: a value computable from the public register alone.
    By construction it CANNOT read the secret. -/
inductive PExpr
  | pub                       -- read the public register
  | lit (n : Val)             -- a constant
  | add (a b : PExpr)         -- addition
deriving DecidableEq, Repr

/-- Evaluate a public expression.  It takes ONLY the public value, so its result is,
    structurally, independent of the secret. -/
def peval : PExpr → Val → Val
  | .pub,     p => p
  | .lit n,   _ => n
  | .add a b, p => peval a p + peval b p

/-- A leakage observation: either a branch decision (timing side channel) or an accessed
    memory address (cache side channel).  This is the attacker-visible alphabet. -/
inductive Obs
  | branch (b : Bool)         -- a branch outcome became observable (timing)
  | addr   (a : Val)          -- a memory address was accessed (cache)
deriving DecidableEq, Repr

/-- The instruction set.  Constant-time primitives (`assignPub`, `branchOnPublic`,
    `condMove`, `loadPub`) never leak the secret through the trace; the two leaky
    primitives (`branchOnSecret`, `loadSecretAddr`) do. -/
inductive Instr
  | assignPub      (e : PExpr)        -- pub := e            (public data flow, no leak)
  | branchOnPublic (e : PExpr)        -- branch on a PUBLIC condition (public-only leak)
  | condMove       (a b : PExpr)      -- CT select: sec := (secret ? b : a); emits NO trace
  | loadPub        (e : PExpr)        -- load at a PUBLIC address (public-only leak)
  | branchOnSecret                    -- LEAKY: branch on the secret
  | loadSecretAddr                    -- LEAKY: load at the secret address
deriving DecidableEq, Repr

/-- A program is a straight-line list of instructions. -/
abbrev Program := List Instr

/-- One step: update the state and emit the leakage this instruction produces.

    * `assignPub`      writes a public value into `pub`, emitting nothing.
    * `branchOnPublic` emits a branch observation determined by PUBLIC data.
    * `condMove`       selects between two public values by the SECRET register and stores
                       the result in `sec`, emitting NOTHING — a data-oblivious select.
    * `loadPub`        emits the PUBLIC address it accesses.
    * `branchOnSecret` emits a branch observation determined by the SECRET  (leak!).
    * `loadSecretAddr` emits the SECRET as an accessed address                (leak!). -/
def step (i : Instr) (s : State) : State × List Obs :=
  match i with
  | .assignPub e      => ({ s with pub := peval e s.pub }, [])
  | .branchOnPublic e => (s, [Obs.branch (decide (peval e s.pub = 0))])
  | .condMove a b     => ({ s with sec := if s.sec = 0 then peval a s.pub else peval b s.pub }, [])
  | .loadPub e        => (s, [Obs.addr (peval e s.pub)])
  | .branchOnSecret   => (s, [Obs.branch (decide (s.sec = 0))])
  | .loadSecretAddr   => (s, [Obs.addr s.sec])

/-- Execute a program, threading the state and concatenating the leakage traces. -/
def exec : Program → State → State × List Obs
  | [],      s => (s, [])
  | i :: rest, s =>
      ((exec rest (step i s).1).1, (step i s).2 ++ (exec rest (step i s).1).2)

/-- A single instruction is constant-time iff it is neither of the two leaky primitives. -/
def ctInstr : Instr → Bool
  | .branchOnSecret => false
  | .loadSecretAddr => false
  | _               => true

/-- A program is constant-time iff every instruction is. -/
def ctProgram (P : Program) : Prop := ∀ i ∈ P, ctInstr i = true

/-- **Step-level noninterference.**  For a constant-time instruction, states agreeing on
    the public register produce equal leakage AND still agree on the public register
    afterwards.  (They may diverge on the secret — e.g. `condMove` — which the trace
    never sees.) -/
theorem step_pub_obs (i : Instr) (hi : ctInstr i = true) (s t : State)
    (hpub : s.pub = t.pub) :
    (step i s).1.pub = (step i t).1.pub ∧ (step i s).2 = (step i t).2 := by
  cases i with
  | assignPub e      => simp [step, hpub]
  | branchOnPublic e => simp [step, hpub]
  | condMove a b     => simp [step, hpub]
  | loadPub e        => simp [step, hpub]
  | branchOnSecret   => simp [ctInstr] at hi
  | loadSecretAddr   => simp [ctInstr] at hi

/-- **Program-level noninterference invariant** (proved by induction on the program):
    a constant-time program run from two states agreeing on the public register yields
    equal final public registers AND equal leakage traces. -/
theorem exec_pub_trace_inv :
    ∀ (P : Program), ctProgram P → ∀ (s t : State), s.pub = t.pub →
      (exec P s).1.pub = (exec P t).1.pub ∧ (exec P s).2 = (exec P t).2 := by
  intro P
  induction P with
  | nil => intro _ s t hpub; exact ⟨hpub, rfl⟩
  | cons i rest ih =>
      intro hct s t hpub
      have hi : ctInstr i = true := hct i (by simp)
      have hrest : ctProgram rest := fun j hj => hct j (by simp [hj])
      obtain ⟨hstep_pub, hstep_obs⟩ := step_pub_obs i hi s t hpub
      obtain ⟨hrec_pub, hrec_obs⟩ := ih hrest (step i s).1 (step i t).1 hstep_pub
      refine ⟨hrec_pub, ?_⟩
      show (step i s).2 ++ (exec rest (step i s).1).2
         = (step i t).2 ++ (exec rest (step i t).1).2
      rw [hstep_obs, hrec_obs]

/-- **THE CONSTANT-TIME NONINTERFERENCE THEOREM.**
    For a constant-time program, the observable trace depends ONLY on the public part:
    two states with the same `pub` (and arbitrary `sec`) produce the SAME trace.
    This is the formal definition of "constant-time / no timing side channel". -/
theorem ct_trace_noninterference (P : Program) (hct : ctProgram P) (s t : State)
    (hpub : s.pub = t.pub) :
    (exec P s).2 = (exec P t).2 :=
  (exec_pub_trace_inv P hct s t hpub).2

/-- **LEAKY COUNTEREXAMPLE (teeth).**  A program using `branchOnSecret` whose trace
    DIFFERS for two states agreeing on the public register but differing on the secret.
    So the `ctProgram` restriction is necessary, not vacuous. -/
theorem leaky_program_leaks :
    ∃ (P : Program) (s t : State), s.pub = t.pub ∧ (exec P s).2 ≠ (exec P t).2 :=
  ⟨[Instr.branchOnSecret], ⟨0, 0⟩, ⟨0, 1⟩, rfl, by decide⟩

/-- **Functional correctness preserved.**  The data-oblivious `condMove` computes exactly
    the value a secret-dependent branch would — same result — into the secret register. -/
theorem condMove_correct (a b : PExpr) (s : State) :
    (exec [Instr.condMove a b] s).1.sec
      = (if s.sec = 0 then peval a s.pub else peval b s.pub) := rfl

/-- ... yet it emits an EMPTY trace: the secret-driven select leaks nothing. -/
theorem condMove_no_leak (a b : PExpr) (s : State) :
    (exec [Instr.condMove a b] s).2 = [] := rfl

/-! ## Non-vacuity witnesses (concrete `decide`/`rfl`). -/

/-- A concrete constant-time program (uses `condMove` on the secret, then a public load
    and a public branch). -/
def ctDemo : Program :=
  [Instr.condMove (PExpr.lit 7) (PExpr.lit 9),
   Instr.loadPub PExpr.pub,
   Instr.branchOnPublic PExpr.pub]

/-- It really is a constant-time program. -/
example : ctProgram ctDemo := by unfold ctProgram ctDemo; decide

/-- Non-vacuity of the CT side: the trace is IDENTICAL for two states that agree on the
    public register (5) but differ on the secret (0 vs 1). -/
example : (exec ctDemo ⟨5, 0⟩).2 = (exec ctDemo ⟨5, 1⟩).2 := by decide

/-- And the ct-noninterference theorem delivers this for `ctDemo` abstractly. -/
example : (exec ctDemo ⟨5, 0⟩).2 = (exec ctDemo ⟨5, 42⟩).2 :=
  ct_trace_noninterference ctDemo (by unfold ctProgram ctDemo; decide) ⟨5, 0⟩ ⟨5, 42⟩ rfl

/-- The condMove select still yields the correct (secret-dependent) result value. -/
example : (exec ctDemo ⟨5, 0⟩).1.sec = 7 := by decide
example : (exec ctDemo ⟨5, 1⟩).1.sec = 9 := by decide

/-- Non-vacuity of the leaky side: a `branchOnSecret` trace DIFFERS for two secrets. -/
example : (exec [Instr.branchOnSecret] ⟨0, 0⟩).2 ≠ (exec [Instr.branchOnSecret] ⟨0, 1⟩).2 := by
  decide

end Brockian.HighAssurance.ConstantTime
