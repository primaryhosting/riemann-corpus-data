import Mathlib

/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Words and tapes

Languages are sets of finite binary strings.  Machines work on a one-sided-infinite-free,
two-way infinite tape over the alphabet `Option Bool`, where `none` is the blank symbol.
We reuse Mathlib's `Turing.Tape` for the tape datatype. -/

/-- A binary word: the inputs of our machines. -/
abbrev Word : Type := List Bool

/-- The tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Alph : Type := Option Bool

/-- The initial tape holding the input word `x`, with the head on its first cell. -/
def initTape (x : Word) : Turing.Tape Alph := Turing.Tape.mk₁ (x.map some)

/-! ## Deterministic Turing machines -/

/-- A deterministic one-tape Turing machine over the alphabet `Alph`, with a finite set of
states, an initial state, a distinguished accepting state, and a transition function which,
given the current state and the scanned symbol, returns the new state, the symbol to be
written, and the direction in which the head moves. -/
structure DTM where
  /-- The (finite) set of states. -/
  State : Type
  /-- Finiteness of the state set. -/
  stateFinite : Fintype State
  /-- The initial state. -/
  start : State
  /-- The accepting state. -/
  accept : State
  /-- The transition function. -/
  δ : State → Alph → State × Alph × Turing.Dir

/-- A configuration of a deterministic machine: current state together with the tape. -/
abbrev DTM.Cfg (M : DTM) : Type := M.State × Turing.Tape Alph

/-- One computation step of a deterministic machine. -/
def DTM.step (M : DTM) (c : M.Cfg) : M.Cfg :=
  let r := M.δ c.1 c.2.head
  (r.1, (c.2.write r.2.1).move r.2.2)

/-- The initial configuration of `M` on input `x`. -/
def DTM.init (M : DTM) (x : Word) : M.Cfg := (M.start, initTape x)

/-- `M` accepts `x` within `t` steps: running `M` from its initial configuration on `x`,
the accepting state is reached after at most `t` steps. -/
def DTM.AcceptsIn (M : DTM) (x : Word) (t : ℕ) : Prop :=
  ∃ s ≤ t, (M.step^[s] (M.init x)).1 = M.accept

/-! ## Nondeterministic Turing machines -/

/-- A nondeterministic one-tape Turing machine: as `DTM`, except that the transition
function returns a *set* of possible successor triples. -/
structure NTM where
  /-- The (finite) set of states. -/
  State : Type
  /-- Finiteness of the state set. -/
  stateFinite : Fintype State
  /-- The initial state. -/
  start : State
  /-- The accepting state. -/
  accept : State
  /-- The transition relation, given as a set of possible moves. -/
  δ : State → Alph → Set (State × Alph × Turing.Dir)

/-- A configuration of a nondeterministic machine. -/
abbrev NTM.Cfg (N : NTM) : Type := N.State × Turing.Tape Alph

/-- The one-step relation of a nondeterministic machine. -/
def NTM.Step (N : NTM) (c c' : N.Cfg) : Prop :=
  ∃ r ∈ N.δ c.1 c.2.head, c' = (r.1, (c.2.write r.2.1).move r.2.2)

/-- The initial configuration of `N` on input `x`. -/
def NTM.init (N : NTM) (x : Word) : N.Cfg := (N.start, initTape x)

/-- `N` accepts `x` within `t` steps: there is a computation path of length `s ≤ t`
starting in the initial configuration on `x` and ending in the accepting state. -/
def NTM.AcceptsIn (N : NTM) (x : Word) (t : ℕ) : Prop :=
  ∃ s ≤ t, ∃ path : ℕ → N.Cfg,
    path 0 = N.init x ∧ (∀ i < s, N.Step (path i) (path (i + 1))) ∧ (path s).1 = N.accept

/-! ## The complexity classes `P` and `NP` -/

/-- The class `P`: languages decided by a deterministic Turing machine whose running time
is bounded by a polynomial in the length of the input.  Concretely, `L ∈ ClassP` iff there
are a deterministic machine `M` and constants `c, k` such that a word `x` belongs to `L`
exactly when `M` accepts `x` within `c * (|x| + 1) ^ k` steps. -/
def ClassP : Set (Set Word) :=
  {L | ∃ (M : DTM) (c k : ℕ), ∀ x : Word, x ∈ L ↔ M.AcceptsIn x (c * (x.length + 1) ^ k)}

/-- The class `NP`: languages accepted by a nondeterministic Turing machine within a
polynomial number of steps. -/
def ClassNP : Set (Set Word) :=
  {L | ∃ (N : NTM) (c k : ℕ), ∀ x : Word, x ∈ L ↔ N.AcceptsIn x (c * (x.length + 1) ^ k)}

/-! ## Polynomial-time reducibility -/

/-- A pairing of two words: the bits of `x` are doubled (each bit `b` becomes `true, b`),
then the separator `false, false` is emitted, then `w` follows verbatim. -/
def pairWord (x w : Word) : Word := (x.flatMap fun b => [true, b]) ++ [false, false] ++ w

/-- The *bit graph* of a function `f : Word → Word`: the language of all pairs `(x, 1 ^ i)`
such that the `i`-th bit of `f x` exists and equals `true`. -/
def bitGraph (f : Word → Word) : Set Word :=
  {z | ∃ (x : Word) (i : ℕ), (f x)[i]? = some true ∧ z = pairWord x (List.replicate i true)}

/-- `f : Word → Word` is polynomial-time computable: its output length is polynomially
bounded in its input length, and its bit graph is decidable in polynomial time. -/
def PolyTimeComputable (f : Word → Word) : Prop :=
  (∃ c k : ℕ, ∀ x : Word, (f x).length ≤ c * (x.length + 1) ^ k) ∧ bitGraph f ∈ ClassP

/-- Polynomial-time many-one (Karp) reducibility: `A ≤ₚ B` iff there is a polynomial-time
computable function `f` with `x ∈ A ↔ f x ∈ B`. -/
def PolyReducible (A B : Set Word) : Prop :=
  ∃ f : Word → Word, PolyTimeComputable f ∧ ∀ x : Word, x ∈ A ↔ f x ∈ B

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyReducible

/-- A language is `NP`-hard if every language in `NP` reduces to it in polynomial time. -/
def NPHard (L : Set Word) : Prop := ∀ A ∈ ClassNP, A ≤ₚ L

/-- A language is `NP`-complete if it lies in `NP` and is `NP`-hard. -/
def NPComplete (L : Set Word) : Prop := L ∈ ClassNP ∧ NPHard L

/-! ## Basic facts and the statement of the P vs NP problem -/

/-- Every deterministic machine can be regarded as a nondeterministic one. -/
def DTM.toNTM (M : DTM) : NTM where
  State := M.State
  stateFinite := M.stateFinite
  start := M.start
  accept := M.accept
  δ := fun q a => {M.δ q a}

theorem DTM.toNTM_acceptsIn {M : DTM} {x : Word} {t : ℕ} (h : M.AcceptsIn x t) :
    M.toNTM.AcceptsIn x t := by
  obtain ⟨s, hs, hacc⟩ := h
  refine ⟨s, hs, fun i => M.step^[i] (M.init x), ?_, ?_, hacc⟩
  · simp [DTM.init, NTM.init, DTM.toNTM]
  · intro i _
    refine ⟨M.δ (M.step^[i] (M.init x)).1 (M.step^[i] (M.init x)).2.head, rfl, ?_⟩
    simp only [Function.iterate_succ_apply']
    rfl

/-- `P ⊆ NP`: a language decided by a polynomially time-bounded deterministic machine is
accepted by a polynomially time-bounded nondeterministic machine. -/
theorem ClassP_subset_ClassNP : ClassP ⊆ ClassNP := by
  rintro L ⟨M, c, k, hM⟩
  exact ⟨M.toNTM, c, k, fun x => (hM x).trans ⟨DTM.toNTM_acceptsIn, fun h => by
    obtain ⟨s, hs, path, h0, hstep, hacc⟩ := h
    refine ⟨s, hs, ?_⟩
    have key : ∀ i ≤ s, path i = M.step^[i] (M.init x) := by
      intro i hi
      induction i with
      | zero => simpa [DTM.init, NTM.init, DTM.toNTM] using h0
      | succ n ih =>
          obtain ⟨r, hr, hpath⟩ := hstep n (by omega)
          rw [hpath, ih (by omega), Function.iterate_succ_apply']
          have : r = M.δ (M.step^[n] (M.init x)).1 (M.step^[n] (M.init x)).2.head := by
            have := hr
            simp only [DTM.toNTM, Set.mem_singleton_iff] at this
            rw [this, ih (by omega)]
          rw [this]
          rfl
    rw [← key s le_rfl]
    exact hacc⟩⟩

/-- **The P vs NP problem.**

`P ≠ NP` — the assertion that the classes of languages decidable in deterministic
polynomial time and acceptable in nondeterministic polynomial time differ — is equivalent
to the existence of a language which is accepted by some polynomially time-bounded
nondeterministic Turing machine but is decided by no polynomially time-bounded
deterministic Turing machine.

This theorem records the precise statement of the open problem (whose truth value is *not*
settled here) in the two standard equivalent forms; the equivalence itself follows from
`ClassP ⊆ ClassNP`. -/
theorem P_vs_NP_statement :
    ClassP ≠ ClassNP ↔ ∃ L : Set Word, L ∈ ClassNP ∧ L ∉ ClassP := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (subset_antisymm ClassP_subset_ClassNP hc)
  · rintro ⟨L, hNP, hP⟩ h
    exact hP (h ▸ hNP)

end Frontier

