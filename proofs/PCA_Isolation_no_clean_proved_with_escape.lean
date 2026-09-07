import Mathlib

/-!
# Proof-Carrying Apps — Isolation (`PCA.Isolation` namespace)

Category: Proof-Carrying Apps
Provenance: Aristotle theorem prover (Harmonic); assembled from individual
AXLE-verified best-proof files into one registered module.

Each target theorem below was proved in its own self-contained file against its
own isolation model; the models are genuinely different (guard formulas, a
domain/depth scope encoding, capability traces, a heap-reachability isolate, a
privilege-escalation closure, and a state-predicate refinement).  They are kept
here in independent `section`s so their local definitions do not collide, while
every theorem retains its exact `PCA.Isolation.*` name and verbatim statement.

Note: `PCA.Isolation.in_scope_encoding_sound` (the path-prefix / boolean
decision-procedure encoding) is **excluded** from this module: its helper
`Scope`/`InScope` re-declare, with a different signature, the ones used by
`in_scope_encoding_complete`, and its helper `Policy` clashes with the one used
by `no_clean_proved_with_escape`.  It cannot share this namespace without either
renaming those helpers (which would alter its verbatim statement) or a
sub-namespace (which would rename the theorem).  It remains available as a
standalone file / its own module.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-! ## Guard-formula disjunction split -/

section GuardModel

/-- Guard formulas of the isolation engine's policy language: propositional
formulas over atomic capability checks indexed by natural numbers. -/
inductive Guard : Type
  | tt : Guard
  | ff : Guard
  | atom : Nat → Guard
  | neg : Guard → Guard
  | conj : Guard → Guard → Guard
  | disj : Guard → Guard → Guard
  deriving DecidableEq, Repr

namespace Guard

/-- Semantics of a guard relative to an environment assigning a truth value to
each atomic capability check. -/
def eval (env : Nat → Bool) : Guard → Bool
  | tt => true
  | ff => false
  | atom i => env i
  | neg g => !(g.eval env)
  | conj g₁ g₂ => (g₁.eval env) && (g₂.eval env)
  | disj g₁ g₂ => (g₁.eval env) || (g₂.eval env)

/-- The isolation engine's disjunction split: a guard is decomposed into the
list of its top-level disjuncts, each of which is analysed in isolation. -/
def split : Guard → List Guard
  | disj g₁ g₂ => g₁.split ++ g₂.split
  | g => [g]

@[simp] theorem split_disj (g₁ g₂ : Guard) :
    (disj g₁ g₂).split = g₁.split ++ g₂.split := rfl

/-- The split is never empty: every guard has at least one branch. -/
theorem split_ne_nil (g : Guard) : g.split ≠ [] := by
  induction g with
  | disj g₁ g₂ ih₁ _ => simpa [split] using fun h => ih₁ (List.append_eq_nil_iff.mp h).1
  | _ => simp [split]

end Guard

/-- **Disjunction split preserves semantics.**  Splitting a guard into its
top-level disjuncts, as the isolation engine does before analysing each branch
separately, is both sound and complete with respect to the guard semantics: the
guard holds in an environment exactly when one of its branches does. -/
theorem disjunction_split_preserves_semantics (env : Nat → Bool) (g : Guard) :
    g.eval env = true ↔ ∃ b ∈ g.split, b.eval env = true := by
  induction g with
  | disj g₁ g₂ ih₁ ih₂ =>
      simp only [Guard.eval, Guard.split_disj, List.mem_append, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨b, hb, hb'⟩ := ih₁.mp h
          exact ⟨b, Or.inl hb, hb'⟩
        · obtain ⟨b, hb, hb'⟩ := ih₂.mp h
          exact ⟨b, Or.inr hb, hb'⟩
      · rintro ⟨b, hb | hb, hb'⟩
        · exact Or.inl (ih₁.mpr ⟨b, hb, hb'⟩)
        · exact Or.inr (ih₂.mpr ⟨b, hb, hb'⟩)
  | _ => simp [Guard.split]

/-- Soundness direction: if some branch of the split holds, the original guard
holds. -/
theorem split_sound (env : Nat → Bool) (g : Guard) (b : Guard)
    (hb : b ∈ g.split) (h : b.eval env = true) : g.eval env = true :=
  (disjunction_split_preserves_semantics env g).mpr ⟨b, hb, h⟩

/-- Completeness direction: if the guard holds, some branch of the split
holds. -/
theorem split_complete (env : Nat → Bool) (g : Guard) (h : g.eval env = true) :
    ∃ b ∈ g.split, b.eval env = true :=
  (disjunction_split_preserves_semantics env g).mp h

end GuardModel

/-! ## In-scope encoding (domain / depth model) — completeness -/

section EncodingModel

/-- A resource the isolation engine may be asked to mediate access to:
a domain (the isolation boundary it lives behind) together with a path inside it. -/
structure Resource where
  domain : String
  path : List String
  deriving DecidableEq, Repr

/-- An isolation scope: a list of permitted domains together with a maximal path depth. -/
structure Scope where
  allowed : List String
  maxDepth : Nat
  deriving Repr

/-- A resource is *in scope* when its domain is permitted and its path is not too deep. -/
def InScope (sc : Scope) (r : Resource) : Prop :=
  r.domain ∈ sc.allowed ∧ r.path.length ≤ sc.maxDepth

instance (sc : Scope) (r : Resource) : Decidable (InScope sc r) := by
  unfold InScope; infer_instance

/-- The engine's wire encoding: an in-scope resource is encoded as the flat token list
`domain :: path`; an out-of-scope resource has no encoding at all. -/
def encode (sc : Scope) (r : Resource) : Option (List String) :=
  if InScope sc r then some (r.domain :: r.path) else none

/-- Decoding a token list back into a resource. The empty list is not a valid encoding. -/
def decode : List String → Option Resource
  | [] => none
  | d :: p => some ⟨d, p⟩

/-- Decoding inverts encoding on every value the encoder actually produces. -/
theorem decode_encode (sc : Scope) (r : Resource) (c : List String)
    (h : encode sc r = some c) : decode c = some r := by
  unfold encode at h
  by_cases hs : InScope sc r
  · rw [if_pos hs] at h
    obtain rfl := Option.some.inj h
    cases r
    rfl
  · rw [if_neg hs] at h
    exact absurd h (by simp)

/-- The encoder is defined exactly on the in-scope resources: it succeeds if and only if
the resource is in scope, and in that case the encoding faithfully determines the resource.

This is the completeness (every in-scope resource is representable) and soundness
(nothing out of scope is representable) statement for the isolation engine's model. -/
theorem in_scope_encoding_complete (sc : Scope) (r : Resource) :
    InScope sc r ↔ ∃ c, encode sc r = some c ∧ decode c = some r := by
  constructor
  · intro hs
    refine ⟨r.domain :: r.path, ?_, ?_⟩
    · simp [encode, if_pos hs]
    · cases r; rfl
  · rintro ⟨c, hc, -⟩
    by_contra hs
    rw [encode, if_neg hs] at hc
    exact absurd hc (by simp)

/-- Encoding is injective on in-scope resources: distinct in-scope resources never
collide on the wire. -/
theorem encode_injOn (sc : Scope) {r₁ r₂ : Resource} {c : List String}
    (h₁ : encode sc r₁ = some c) (h₂ : encode sc r₂ = some c) : r₁ = r₂ := by
  have d₁ := decode_encode sc r₁ c h₁
  have d₂ := decode_encode sc r₂ c h₂
  have : some r₁ = some r₂ := d₁ ▸ d₂ ▸ rfl
  exact Option.some.inj this

/-- Out-of-scope resources have no encoding. -/
theorem encode_eq_none_of_not_inScope (sc : Scope) (r : Resource) (h : ¬ InScope sc r) :
    encode sc r = none := by
  simp [encode, if_neg h]

end EncodingModel

/-! ## Capability-trace sandbox — no clean proved run escapes -/

section CapabilityModel

/-- A capability is an abstract resource token that the isolation engine mediates. -/
abbrev Cap := Nat

/-- An application, described by the list of capabilities it *declares* it will use.
This declaration is what the proof carried by the app talks about. -/
structure App where
  declared : List Cap
  deriving DecidableEq

/-- A sandbox policy, described by the list of capabilities the isolation engine actually
*grants* at run time. -/
structure Policy where
  granted : List Cap
  deriving DecidableEq

/-- An execution trace is the list of capabilities exercised, in order. -/
abbrev Trace := List Cap

/-- A trace is *clean* for an app when every capability it exercises was declared. -/
def Clean (a : App) (t : Trace) : Prop := ∀ c ∈ t, c ∈ a.declared

/-- An app is *proved* against a policy when its carried certificate checks out, i.e. every
declared capability is granted by the policy. -/
def Proved (p : Policy) (a : App) : Prop := ∀ c ∈ a.declared, c ∈ p.granted

/-- A trace *escapes* the sandbox when it exercises some capability that is not granted. -/
def Escapes (p : Policy) (t : Trace) : Prop := ∃ c ∈ t, c ∉ p.granted

instance (a : App) (t : Trace) : Decidable (Clean a t) := by
  unfold Clean; infer_instance

instance (p : Policy) (a : App) : Decidable (Proved p a) := by
  unfold Proved; infer_instance

instance (p : Policy) (t : Trace) : Decidable (Escapes p t) := by
  unfold Escapes; infer_instance

/-- **Main theorem (soundness).** No clean run of a proved app ever escapes the sandbox:
if every capability used was declared, and every declared capability is granted, then no
used capability can be ungranted. -/
theorem no_clean_proved_with_escape
    (p : Policy) (a : App) (t : Trace)
    (hc : Clean a t) (hp : Proved p a) : ¬ Escapes p t := by
  rintro ⟨c, hct, hcg⟩
  exact hcg (hp c (hc c hct))

/-- Predicate-level restatement: no triple `(app, trace)` is simultaneously clean, proved
and escaping. -/
theorem no_clean_proved_escaping_triple (p : Policy) :
    ∀ x : App × Trace, ¬ (Clean x.1 x.2 ∧ Proved p x.1 ∧ Escapes p x.2) := by
  rintro ⟨a, t⟩ ⟨hc, hp, he⟩
  exact no_clean_proved_with_escape p a t hc hp he

/-- Contrapositive form: an escaping run means either the app misbehaved (it used an
undeclared capability) or its certificate does not check out against the policy. -/
theorem escape_imp_not_clean_or_not_proved
    (p : Policy) (a : App) (t : Trace) (he : Escapes p t) :
    ¬ Clean a t ∨ ¬ Proved p a := by
  by_cases hc : Clean a t
  · exact Or.inr fun hp => no_clean_proved_with_escape p a t hc hp he
  · exact Or.inl hc

/-- Decidable de Morgan for bounded universal quantification over a list. -/
private theorem exists_not_of_not_forall_mem
    {P : Cap → Prop} [DecidablePred P] :
    ∀ {l : List Cap}, ¬ (∀ c ∈ l, P c) → ∃ c ∈ l, ¬ P c
  | [], h => absurd (by intro c hc; cases hc) h
  | b :: l, h => by
      by_cases hb : P b
      · have h' : ¬ (∀ c ∈ l, P c) := by
          intro hall
          exact h (by
            intro c hc
            cases hc with
            | head => exact hb
            | tail _ hc => exact hall c hc)
        obtain ⟨c, hc, hnc⟩ := exists_not_of_not_forall_mem h'
        exact ⟨c, List.mem_cons_of_mem _ hc, hnc⟩
      · exact ⟨b, List.mem_cons_self .., hb⟩

/-- If an app's certificate fails (some declared capability is not granted) then there is a
*clean* trace of that app which escapes.  Hence the hypothesis `Proved` in the main theorem
cannot be dropped. -/
theorem exists_clean_escape_of_not_proved
    (p : Policy) (a : App) (hp : ¬ Proved p a) :
    ∃ t : Trace, Clean a t ∧ Escapes p t := by
  obtain ⟨c, hcd, hcg⟩ := exists_not_of_not_forall_mem (P := fun c => c ∈ p.granted) hp
  refine ⟨[c], ?_, ⟨c, List.mem_cons_self .., hcg⟩⟩
  intro d hd
  cases hd with
  | head => exact hcd
  | tail _ hd => cases hd

/-- If some capability lies outside the policy then escaping traces exist at all; for a
proved app such a trace is necessarily unclean.  Hence the hypothesis `Clean` in the main
theorem cannot be dropped either. -/
theorem exists_escape_of_ungranted
    (p : Policy) {c : Cap} (hc : c ∉ p.granted) :
    ∃ t : Trace, Escapes p t :=
  ⟨[c], c, List.mem_cons_self .., hc⟩

/-- Full characterisation of sandbox safety for a run: a trace fails to escape exactly when
every capability it exercises is granted. -/
theorem not_escapes_iff (p : Policy) (t : Trace) :
    ¬ Escapes p t ↔ ∀ c ∈ t, c ∈ p.granted := by
  constructor
  · intro h c hct
    by_cases hcg : c ∈ p.granted
    · exact hcg
    · exact absurd ⟨c, hct, hcg⟩ h
  · rintro h ⟨c, hct, hcg⟩
    exact hcg (h c hct)

end CapabilityModel

/-! ## Heap-reachability isolate — null escape iff unowned reachable -/

section IsolateModel

variable {α : Type*}

/-- An *isolate*: the abstract model used by the isolation engine.

* `edge a b` means the object `a` holds a reference to the object `b`;
* `owned` is the set of objects that belong to (are owned by) the isolate;
* `root` is the isolate's entry object.
-/
structure Isolate (α : Type*) where
  /-- `edge a b` holds when object `a` stores a reference to object `b`. -/
  edge : α → α → Prop
  /-- The set of objects owned by the isolate. -/
  owned : Set α
  /-- The entry object of the isolate. -/
  root : α

/-- `Reaches I a b` : `b` is reachable from `a` by following references. -/
def Reaches (I : Isolate α) : α → α → Prop :=
  Relation.ReflTransGen I.edge

/-- A *null escape trace* is the concrete counterexample the engine produces: a finite
reference trace `root :: l` all of whose consecutive steps are references, whose final
object is **not** owned by the isolate (so the null reference travelling along the trace
leaves the isolate). -/
def EscapeTrace (I : Isolate α) (l : List α) : Prop :=
  List.IsChain I.edge (I.root :: l) ∧
    (I.root :: l).getLast (List.cons_ne_nil _ _) ∉ I.owned

/-- A null reference escapes the isolate when some escape trace exists. -/
def NullEscape (I : Isolate α) : Prop :=
  ∃ l : List α, EscapeTrace I l

/-- **Soundness and completeness of the isolation engine's model.**
A null reference escapes the isolate (i.e. the engine can exhibit a reference trace out of
the isolate) if and only if some object that is not owned by the isolate is reachable from
its root. -/
theorem null_escape_iff_unowned_reachable (I : Isolate α) :
    NullEscape I ↔ ∃ n, Reaches I I.root n ∧ n ∉ I.owned := by
  constructor
  · rintro ⟨l, hchain, hlast⟩
    exact ⟨_, List.relationReflTransGen_of_exists_isChain_cons l hchain rfl, hlast⟩
  · rintro ⟨n, hreach, hn⟩
    obtain ⟨l, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen (r := I.edge) hreach
    exact ⟨l, hchain, by rw [hlast]; exact hn⟩

/-- **Soundness.** If every object reachable from the root is owned by the isolate, then no
null reference can escape it. -/
theorem not_nullEscape_of_forall_reachable_owned (I : Isolate α)
    (h : ∀ n, Reaches I I.root n → n ∈ I.owned) : ¬ NullEscape I := by
  rw [null_escape_iff_unowned_reachable]
  rintro ⟨n, hreach, hn⟩
  exact hn (h n hreach)

/-- **Completeness.** If some unowned object is reachable, the engine can exhibit an escape
trace. -/
theorem nullEscape_of_unowned_reachable (I : Isolate α) {n : α}
    (hreach : Reaches I I.root n) (hn : n ∉ I.owned) : NullEscape I :=
  (null_escape_iff_unowned_reachable I).2 ⟨n, hreach, hn⟩

/-- If the root itself is not owned, a null reference escapes immediately. -/
theorem nullEscape_of_root_not_owned (I : Isolate α) (h : I.root ∉ I.owned) :
    NullEscape I :=
  nullEscape_of_unowned_reachable I Relation.ReflTransGen.refl h

end IsolateModel

/-! ## Privilege-escalation closure — priv escape is monotone -/

section EscalationModel

universe u

/-- `Escalates g a b` : starting from privilege `a`, the isolation engine's
one-step escalation relation `g` allows reaching privilege `b` in finitely many
steps.  This is the reflexive-transitive closure of `g`. -/
inductive Escalates {P : Type u} (g : P → P → Prop) : P → P → Prop
  | refl (a : P) : Escalates g a a
  | tail {a b c : P} : Escalates g a b → g b c → Escalates g a c

namespace Escalates

theorem single {P : Type u} {g : P → P → Prop} {a b : P} (h : g a b) : Escalates g a b :=
  (Escalates.refl a).tail h

theorem trans {P : Type u} {g : P → P → Prop} {a b c : P}
    (hab : Escalates g a b) (hbc : Escalates g b c) : Escalates g a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact ih.tail hstep

/-- Escalation reachability is monotone in the one-step escalation relation. -/
theorem mono {P : Type u} {g h : P → P → Prop} (hgh : ∀ x y, g x y → h x y)
    {a b : P} (hab : Escalates g a b) : Escalates h a b := by
  induction hab with
  | refl => exact Escalates.refl _
  | tail _ hstep ih => exact ih.tail (hgh _ _ hstep)

end Escalates

/-- `escape g S` is the set of privileges an attacker can obtain (i.e. escape to)
from the initial privilege set `S`, using the escalation relation `g`. -/
def escape {P : Type u} (g : P → P → Prop) (S : P → Prop) : P → Prop :=
  fun q => ∃ p, S p ∧ Escalates g p q

/-- Soundness of the model, part 1: the initial privileges are escapable. -/
theorem subset_escape {P : Type u} (g : P → P → Prop) (S : P → Prop) :
    ∀ p, S p → escape g S p :=
  fun p hp => ⟨p, hp, Escalates.refl p⟩

/-- Soundness of the model, part 2: the escape set is closed under escalation. -/
theorem escape_closed {P : Type u} {g : P → P → Prop} {S : P → Prop} {x y : P}
    (hx : escape g S x) (hxy : g x y) : escape g S y := by
  obtain ⟨p, hp, hchain⟩ := hx
  exact ⟨p, hp, hchain.tail hxy⟩

/-- Completeness of the model: `escape g S` is the *least* set of privileges that
contains `S` and is closed under one-step escalation. -/
theorem escape_least {P : Type u} {g : P → P → Prop} {S T : P → Prop}
    (hST : ∀ p, S p → T p) (hclosed : ∀ x y, T x → g x y → T y) :
    ∀ q, escape g S q → T q := by
  rintro q ⟨p, hp, hchain⟩
  induction hchain with
  | refl => exact hST p hp
  | tail _ hstep ih => exact hclosed _ _ ih hstep

/-- **Privilege escape is monotone.**  Enlarging the initial privilege set, or
enlarging the set of permitted escalation steps, can only enlarge the set of
privileges reachable by escape.  Contrapositively: a proof that a privilege is
unreachable under a permissive model transfers to every more restrictive model. -/
theorem priv_escape_monotone {P : Type u} {g h : P → P → Prop} {S T : P → Prop}
    (hgh : ∀ x y, g x y → h x y) (hST : ∀ p, S p → T p) :
    ∀ q, escape g S q → escape h T q := by
  rintro q ⟨p, hp, hchain⟩
  exact ⟨p, hST p hp, hchain.mono hgh⟩

end EscalationModel

/-! ## State-predicate refinement — tightening refines the original -/

section RefinementModel

universe u

/-- A *predicate* of the isolation engine: an admissibility test on engine states. -/
abbrev Pred (σ : Type u) := σ → Prop

/-- `P'` **refines** `P` when every state admitted by `P'` is admitted by `P`,
i.e. the refined predicate is at least as restrictive as the original. -/
def Refines {σ : Type u} (P' P : Pred σ) : Prop := ∀ s, P' s → P s

/-- Tightening a predicate `P` with an extra guard `Q`: a state is admitted by the
tightened predicate exactly when it passes both the original policy and the guard. -/
def tighten {σ : Type u} (P Q : Pred σ) : Pred σ := fun s => P s ∧ Q s

/-- **Main theorem.** The tightened predicate refines the original one: adding a guard
can only shrink the admitted set of states, never enlarge it. -/
theorem tightened_predicate_refines_original {σ : Type u} (P Q : Pred σ) :
    Refines (tighten P Q) P :=
  fun _ h => h.1

/-- **Soundness and completeness** of the tightening construction: the tightened
predicate admits precisely those states admitted by the original predicate that
additionally satisfy the guard. -/
theorem tighten_iff {σ : Type u} (P Q : Pred σ) (s : σ) :
    tighten P Q s ↔ (P s ∧ Q s) := Iff.rfl

/-- Refinement is reflexive. -/
theorem Refines.refl {σ : Type u} (P : Pred σ) : Refines P P := fun _ h => h

/-- Refinement is transitive. -/
theorem Refines.trans {σ : Type u} {P₁ P₂ P₃ : Pred σ}
    (h₁ : Refines P₁ P₂) (h₂ : Refines P₂ P₃) : Refines P₁ P₃ :=
  fun s h => h₂ s (h₁ s h)

/-- Tightening with the guard `Q` is idempotent up to refinement in the other
direction as well: the tightened predicate also refines the guard. -/
theorem tightened_predicate_refines_guard {σ : Type u} (P Q : Pred σ) :
    Refines (tighten P Q) Q :=
  fun _ h => h.2

end RefinementModel

end PCA.Isolation
