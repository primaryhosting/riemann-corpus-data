import Mathlib

/-!
# Lattice noninterference: the real Goguen–Meseguer / Rushby theorem

This file generalizes the two–domain (`low`/`high`) seL4-class confidentiality
demonstrator to an **arbitrary security lattice**. Instead of a single
`high ↛ low` constraint, the information-flow **policy** is now an arbitrary
partial order `flows : L → L → Bool` on a type `L` of security domains
(reflexive + transitive; the concrete instance is also antisymmetric, i.e. a
genuine poset / lattice). This is the setting of Goguen–Meseguer noninterference
as formalised by Rushby via *unwinding conditions*.

The transition relation is faithful to Rushby's model:
  * an `Action` is performed by a domain `dom α`;
  * when it fires it may WRITE only into domains `d'` with `flows (dom α) d'`
    (information flows **upward** only) — enforced *by construction*;
  * the value it writes is computed from the content of **its own domain**
    (`s (dom α)`), i.e. it reads only what it is cleared to read and writes up.

A domain `u` **observes** the content of exactly the domains that flow to it
(`obs u s`, the state restricted to `{d // flows d u}`). Two states are
view-equivalent for `u` when those observations coincide.

We prove the two standard **unwinding conditions**
(`step_consistency`, `local_respect`), lift them along a run, and compose them
by induction to the headline

    `noninterference : obs u (run as s) = obs u (run (as.filter visibleTo u) s)`

— *`u`'s observation depends only on actions from domains that flow to `u`*.
Every step genuinely uses **transitivity** of the policy. The development is
closed with machine-checked non-vacuity witnesses on the concrete 4-element
diamond lattice `⊥ < {l, r} < ⊤` (`l`, `r` incomparable).
-/

namespace Brockian.HighAssurance.LatticeNoninterference

/-- The values stored in each security domain. -/
abbrev Value : Type := ℕ

/-- System state: the content of every security domain. -/
abbrev State (L : Type) : Type := L → Value

/-- An action performed by domain `d`. When it fires it writes, into every
    domain `d'` that `d` may flow to, the value `upd d' (s d)` computed from the
    content of its OWN domain — a faithful "read what you are cleared for, write
    upward" operation (a constant write is the special case `upd d' _ = v`). -/
structure Action (L : Type) where
  d   : L
  upd : L → Value → Value

/-- The domain that performs an action. -/
abbrev dom {L : Type} (α : Action L) : L := α.d

/-- The transition function. The security invariant is visible *by
    construction*: a domain `d'` is touched only when `flows α.d d'`, so
    information can flow only upward. -/
def step {L : Type} (flows : L → L → Bool) (α : Action L) (s : State L) : State L :=
  fun d' => if flows α.d d' then α.upd d' (s α.d) else s d'

/-- What domain `u` observes: the state restricted to the domains that flow to
    `u` (i.e. `s` restricted to `≤ u`). -/
def obs {L : Type} (flows : L → L → Bool) (u : L) (s : State L) :
    {d : L // flows d u = true} → Value :=
  fun d => s d.1

/-- View-equivalence for `u`: two states that `u` cannot tell apart. It is
    literally equality of observations, hence an equivalence relation for free. -/
def viewEq {L : Type} (flows : L → L → Bool) (u : L) (s t : State L) : Prop :=
  obs flows u s = obs flows u t

/-- Pointwise characterisation of view-equivalence. -/
theorem viewEq_iff {L : Type} (flows : L → L → Bool) (u : L) (s t : State L) :
    viewEq flows u s t ↔ ∀ d, flows d u = true → s d = t d := by
  unfold viewEq obs
  constructor
  · intro h d hd
    exact congrFun h ⟨d, hd⟩
  · intro h
    funext d
    exact h d.1 d.2

/-- Run a list of actions, in order, from a starting state (left fold). -/
def run {L : Type} (flows : L → L → Bool) (as : List (Action L)) (s : State L) :
    State L :=
  as.foldl (fun st α => step flows α st) s

@[simp] theorem run_nil {L : Type} (flows : L → L → Bool) (s : State L) :
    run flows [] s = s := rfl

@[simp] theorem run_cons {L : Type} (flows : L → L → Bool)
    (α : Action L) (as : List (Action L)) (s : State L) :
    run flows (α :: as) s = run flows as (step flows α s) := rfl

/-! ## The unwinding conditions -/

/-- **Unwinding condition 1 — step consistency (the weak-step lemma).**
    If `s` and `t` look the same to `u`, then after performing the SAME action
    they still look the same. This genuinely uses **transitivity** of the policy:
    a write into a `u`-visible domain reads from a domain that (by transitivity)
    is itself `u`-visible, so its value agrees on `s` and `t`. -/
theorem step_consistency {L : Type} (flows : L → L → Bool)
    (ftrans : ∀ x y z, flows x y = true → flows y z = true → flows x z = true)
    (α : Action L) {s t : State L} (u : L) (h : viewEq flows u s t) :
    viewEq flows u (step flows α s) (step flows α t) := by
  rw [viewEq_iff] at h ⊢
  intro d hd
  by_cases hb : flows α.d d = true
  · have hαu : flows α.d u = true := ftrans _ _ _ hb hd
    simp only [step, if_pos hb]
    rw [h α.d hαu]
  · simp only [step, if_neg hb]
    exact h d hd

/-- **Unwinding condition 2 — local respect.**
    An action from a domain that does NOT flow to `u` is invisible to `u`: it
    leaves `u`'s observation unchanged. Again uses transitivity: if such an
    action wrote a `u`-visible domain, the writer would flow to `u`. -/
theorem local_respect {L : Type} (flows : L → L → Bool)
    (ftrans : ∀ x y z, flows x y = true → flows y z = true → flows x z = true)
    (α : Action L) (s : State L) (u : L)
    (hflow : flows α.d u = false) :
    viewEq flows u s (step flows α s) := by
  rw [viewEq_iff]
  intro d hd
  by_cases hb : flows α.d d = true
  · exact absurd (ftrans _ _ _ hb hd) (by rw [hflow]; decide)
  · simp only [step, if_neg hb]

/-- Low-equivalence (for any `u`) is preserved along an *entire run*, by
    iterating `step_consistency`. -/
theorem run_consistency {L : Type} (flows : L → L → Bool)
    (ftrans : ∀ x y z, flows x y = true → flows y z = true → flows x z = true)
    (u : L) :
    ∀ (as : List (Action L)) {s t : State L}, viewEq flows u s t →
      viewEq flows u (run flows as s) (run flows as t) := by
  intro as
  induction as with
  | nil => intro s t h; simpa using h
  | cons α as ih =>
      intro s t h
      simp only [run_cons]
      exact ih (step_consistency flows ftrans α u h)

/-! ## The headline theorem -/

/-- **NONINTERFERENCE (Goguen–Meseguer / Rushby, arbitrary lattice).**
    Domain `u`'s final observation depends ONLY on the actions performed by
    domains that flow to `u`: deleting every action from a non-flowing domain
    does not change what `u` sees. Equivalently, actions from domains that do not
    flow to `u` can carry NO information to `u`.

    Proved by genuine induction on the action list, combining `local_respect`
    (for dropped, non-flowing actions) with `step_consistency` lifted to
    `run_consistency`, and transitivity of view-equivalence — the seL4/Rushby
    unwinding architecture, now over an arbitrary security lattice. -/
theorem noninterference {L : Type} (flows : L → L → Bool)
    (ftrans : ∀ x y z, flows x y = true → flows y z = true → flows x z = true)
    (u : L) :
    ∀ (as : List (Action L)) (s : State L),
      obs flows u (run flows as s)
        = obs flows u (run flows (as.filter (fun α => flows (dom α) u)) s) := by
  intro as
  induction as with
  | nil => intro s; simp
  | cons α as ih =>
      intro s
      by_cases hvis : flows (dom α) u = true
      · -- `α` flows to `u`: it is KEPT by the filter.
        have hkeep : (α :: as).filter (fun α => flows (dom α) u)
            = α :: as.filter (fun α => flows (dom α) u) := by
          simp [List.filter_cons, hvis]
        rw [hkeep]
        simp only [run_cons]
        exact ih (step flows α s)
      · -- `α` does not flow to `u`: it is DROPPED, and it is invisible to `u`.
        have hdrop : (α :: as).filter (fun α => flows (dom α) u)
            = as.filter (fun α => flows (dom α) u) := by
          simp [List.filter_cons, hvis]
        have hflow : flows (dom α) u = false := by
          cases hb : flows (dom α) u with
          | true => exact absurd hb hvis
          | false => rfl
        rw [hdrop]
        simp only [run_cons]
        have hlr : obs flows u s = obs flows u (step flows α s) :=
          local_respect flows ftrans α s u hflow
        have hrc : obs flows u (run flows (as.filter (fun α => flows (dom α) u)) s)
            = obs flows u (run flows (as.filter (fun α => flows (dom α) u)) (step flows α s)) :=
          run_consistency flows ftrans u _ hlr
        have hih : obs flows u (run flows as (step flows α s))
            = obs flows u (run flows (as.filter (fun α => flows (dom α) u)) (step flows α s)) :=
          ih (step flows α s)
        exact hih.trans hrc.symm

/-! ## Non-vacuity on a concrete lattice

The 4-element **diamond** security lattice `⊥ < {l, r} < ⊤`, with `l` and `r`
mutually incomparable. Information flows upward: `⊥` is the public/low domain
(it observes only itself), `⊤` is the all-seeing high domain. -/

/-- The four security domains of the diamond lattice. -/
inductive Dom
  | bot | l | r | top
  deriving DecidableEq, Repr, Fintype

/-- The flow policy (partial order) of the diamond lattice: `⊥ ≤ everything`,
    `l ≤ l,⊤`, `r ≤ r,⊤`, `⊤ ≤ ⊤`, and `l`, `r` incomparable. -/
def dflows : Dom → Dom → Bool
  | .bot, _    => true
  | .l,   .l   => true
  | .l,   .top => true
  | .r,   .r   => true
  | .r,   .top => true
  | .top, .top => true
  | _,    _    => false

/-- The policy is a genuine **partial order**: reflexive … -/
theorem dflows_refl : ∀ x, dflows x x = true := by decide

/-- … transitive … -/
theorem dflows_trans :
    ∀ x y z, dflows x y = true → dflows y z = true → dflows x z = true := by decide

/-- … and antisymmetric (hence a real poset, not a mere preorder). -/
theorem dflows_antisymm :
    ∀ x y, dflows x y = true → dflows y x = true → x = y := by decide

/-- Confidentiality constraints really are present: `l` does not flow to `⊥`, and
    `l`, `r` are mutually incomparable. -/
theorem dflows_l_not_bot : dflows .l .bot = false := by decide
theorem dflows_l_r_incomparable : dflows .l .r = false ∧ dflows .r .l = false := by decide

/-- A constant-write action performed by domain `d`. -/
def actWrite (d : Dom) (v : Value) : Action Dom := ⟨d, fun _ _ => v⟩

/-- The all-zero initial state. -/
def s0 : State Dom := fun _ => 0

/-! ### Witness (a): a HIGH action changes high content, yet `⊥` is provably blind -/

/-- A write at the secret domain `l` genuinely CHANGES that domain's content … -/
example : (step dflows (actWrite .l 42) s0) .l = 42 := by decide
example : (step dflows (actWrite .l 42) s0) .l ≠ s0 .l := by decide

/-- … yet the low observer `⊥` cannot detect it at all — a machine-checked
    instance of `local_respect` on the concrete lattice. -/
example : obs dflows .bot s0 = obs dflows .bot (step dflows (actWrite .l 42) s0) :=
  local_respect dflows dflows_trans (actWrite .l 42) s0 .bot (by decide)

/-! ### Witness (b): two runs differing only in incomparable high actions look
identical to `⊥`, though they drive high content to genuinely different values -/

/-- Two runs that differ ONLY in their `l`- and `r`-actions (both incomparable to
    `⊥`, neither flowing to it). -/
def runA : List (Action Dom) := [actWrite .l 7, actWrite .r 9]
def runB : List (Action Dom) := [actWrite .l 1, actWrite .r 2]

/-- `⊥`'s observation is identical across the two runs — a concrete instance of
    the general `noninterference` theorem (both runs filter to the empty run at
    `⊥`). -/
example :
    obs dflows .bot (run dflows runA s0) = obs dflows .bot (run dflows runB s0) := by
  have hA : runA.filter (fun α => dflows (dom α) Dom.bot) = [] := by rfl
  have hB : runB.filter (fun α => dflows (dom α) Dom.bot) = [] := by rfl
  rw [noninterference dflows dflows_trans .bot runA s0,
      noninterference dflows dflows_trans .bot runB s0, hA, hB]

/-- … even though the two runs drive the `l`-domain to genuinely different secret
    values (the confidentiality is real, not degenerate) … -/
example : (run dflows runA s0) .l ≠ (run dflows runB s0) .l := by decide

/-- … and the all-seeing high domain `⊤` (which every domain flows to) DOES see
    the difference — confirming the lattice is genuinely multi-level. -/
example : (run dflows runA s0) .top ≠ (run dflows runB s0) .top := by decide

/-! ### Witness (c): when the policy PERMITS the flow, the low observation responds -/

/-- A write at `⊥` itself (which flows to `⊥` by reflexivity) DOES change what
    `⊥` observes — noninterference is not vacuously true by a constant machine. -/
example : (step dflows (actWrite .bot 5) s0) .bot = 5 := by decide

example : obs dflows .bot s0 ≠ obs dflows .bot (step dflows (actWrite .bot 5) s0) := by
  intro h
  have hb := congrFun h ⟨.bot, by decide⟩
  simp [obs, step, actWrite, s0, dflows] at hb

end Brockian.HighAssurance.LatticeNoninterference
