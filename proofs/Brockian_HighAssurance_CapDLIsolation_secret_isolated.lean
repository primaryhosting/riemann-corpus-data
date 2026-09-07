import Mathlib

/-!
# A Verified capDL Isolation Checker for seL4-based Systems

capDL (Capability Distribution Language) is the language that seL4 static systems
(microkit / CAmkES) compile to: it describes the *initial* capability layout of a
system as a graph of objects (CNodes, TCBs, Frames, Endpoints, …) and the
capabilities each object holds to other objects.  seL4's isolation guarantees are
only as good as this initial layout — yet nothing in the seL4 ecosystem formally
*checks* that a given capDL spec actually enforces the intended isolation
architecture (i.e. that subsystems are confined to their protection domains).

This module fills that gap.  It provides:

* a faithful model of a capDL spec as a capability graph plus a protection-domain
  assignment and a domain-connection policy;
* a **decidable checker** `checkIsolation`;
* a machine-checked **soundness + completeness** theorem `checkIsolation_correct`,
  so a `true` verdict is a certificate that the spec enforces the policy;
* **static-confinement** consequences (`names_only_permitted`, `no_cross_domain_cap`):
  in a well-isolated spec an object cannot even *name* an object in a
  non-permitted domain;
* **transitive isolation** (`isolated_domain_unreachable` /
  `..._into`): an object in a fully-isolated protection domain can never reach —
  through *any* chain of capabilities — an object outside it, and vice versa;
* a concrete, non-vacuous microkit-style 2-domain-plus-secret witness where a
  well-wired spec is accepted (`goodSys_passes`), a mis-wired spec is rejected
  (`badSys_rejected`), and the isolated secret domain is provably unreachable
  (`secret_unreachable_from_app`).

Everything is proved with `decide`/`omega`/structural induction — no `sorry`,
no `admit`, no `native_decide`, and axiom-clean.
-/

namespace Brockian.HighAssurance.CapDLIsolation

/-! ## Model -/

/-- Object identifiers.  Real capDL objects — CNodes, TCBs, Frames, Endpoints,
    Notifications, … — are abstracted to their ids. -/
abbrev Obj := ℕ

/-- Access rights carried by a capability (seL4's read/write/grant plus the
    endpoint verbs recv/send).  Included for fidelity; the isolation architecture
    is enforced at the object-naming level, so edges below need not carry them. -/
inductive Rights where
  | read | write | grant | recv | send
  deriving DecidableEq, Repr

/-- A capDL spec, viewed as a capability graph.  `objs` are the objects in the
    system; an edge `(a, b) ∈ caps` means "object `a` holds a capability that
    names object `b`" (so `a` has some authority over `b`). -/
structure CapDL where
  objs : Finset Obj
  caps : Finset (Obj × Obj)

/-! ## The isolation predicate and its decidable checker -/

/-- `WellIsolated C dom policy` holds when every capability edge stays within the
    permitted domain-connection policy: whenever object `a` names object `b`, the
    protection domain of `a` is allowed by `policy` to connect to that of `b`.
    Cross-domain capabilities exist only where the architecture permits them. -/
def WellIsolated (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool) : Prop :=
  ∀ e ∈ C.caps, policy (dom e.1) (dom e.2) = true

/-- The decidable isolation checker: it decides `WellIsolated` over the finite set
    of capability edges. -/
def checkIsolation (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool) : Bool :=
  decide (∀ e ∈ C.caps, policy (dom e.1) (dom e.2) = true)

/-- **Soundness + completeness of the checker (the certifier).**
    `checkIsolation` returns `true` *iff* the spec is well-isolated.  Hence a
    `true` verdict is a machine-checked certificate that the capDL spec enforces
    the domain-connection policy, and a `false` verdict is a genuine violation. -/
theorem checkIsolation_correct
    (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool) :
    checkIsolation C dom policy = true ↔ WellIsolated C dom policy := by
  unfold checkIsolation WellIsolated
  simp only [decide_eq_true_eq]

/-! ## Static confinement consequences -/

/-- **Static confinement (clean form).**  In a well-isolated spec, if `a` names `b`
    then the policy permits `a`'s domain to connect to `b`'s domain. -/
theorem names_only_permitted
    (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool)
    (hwi : WellIsolated C dom policy) (a b : Obj) (hcap : (a, b) ∈ C.caps) :
    policy (dom a) (dom b) = true :=
  hwi (a, b) hcap

/-- **No cross-domain capability.**  In a well-isolated spec there is *no*
    capability edge between domains the policy forbids — an object cannot even
    name an object in a non-connected domain. -/
theorem no_cross_domain_cap
    (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool)
    (hwi : WellIsolated C dom policy) (a b : Obj)
    (hcap : (a, b) ∈ C.caps) (hno : policy (dom a) (dom b) = false) : False := by
  have h := names_only_permitted C dom policy hwi a b hcap
  rw [h] at hno
  exact Bool.noConfusion hno

/-! ## Transitive isolation (reachability) -/

/-- `Reaches C a b`: object `b` is reachable from object `a` by following a chain
    of capabilities (`a` names `x₁`, `x₁` names `x₂`, …, naming `b`).  This is the
    transitive authority relation of the capability graph. -/
def Reaches (C : CapDL) (a b : Obj) : Prop :=
  Relation.ReflTransGen (fun x y => (x, y) ∈ C.caps) a b

/-- **Transitive isolation — outbound.**  If protection domain `d0` is fully
    isolated by the policy (it may not connect to, and may not be connected to by,
    any other domain), then in a well-isolated spec no object in `d0` can reach —
    through any chain of capabilities — an object outside `d0`.  Proved by
    induction on the reachability chain, using `names_only_permitted` at each edge:
    every object reachable from a `d0`-object stays in `d0`. -/
theorem isolated_domain_unreachable
    (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool)
    (hwi : WellIsolated C dom policy)
    (d0 : ℕ)
    (hiso : ∀ d, d ≠ d0 → policy d0 d = false ∧ policy d d0 = false)
    (a b : Obj) (hda : dom a = d0) (hdb : dom b ≠ d0) :
    ¬ Reaches C a b := by
  intro hreach
  -- Invariant: every object reachable from `a` stays inside `d0`.
  have key : ∀ x, Relation.ReflTransGen (fun x y => (x, y) ∈ C.caps) a x → dom x = d0 := by
    intro x hx
    induction hx with
    | refl => exact hda
    | tail _ h₂ ih =>
        -- ih : the source stays in `d0`; h₂ : the new edge; goal : the target stays in `d0`.
        have hedge := names_only_permitted C dom policy hwi _ _ h₂
        by_contra hne
        have hfalse := (hiso _ hne).1
        rw [ih] at hedge
        rw [hedge] at hfalse
        exact Bool.noConfusion hfalse
  exact hdb (key b hreach)

/-- **Transitive isolation — inbound.**  Dually: if `d0` is fully isolated, then no
    object *outside* `d0` can reach an object *inside* `d0`.  Every object reachable
    from an outside object stays outside `d0`. -/
theorem isolated_domain_unreachable_into
    (C : CapDL) (dom : Obj → ℕ) (policy : ℕ → ℕ → Bool)
    (hwi : WellIsolated C dom policy)
    (d0 : ℕ)
    (hiso : ∀ d, d ≠ d0 → policy d0 d = false ∧ policy d d0 = false)
    (a b : Obj) (hda : dom a ≠ d0) (hdb : dom b = d0) :
    ¬ Reaches C a b := by
  intro hreach
  have key : ∀ x, Relation.ReflTransGen (fun x y => (x, y) ∈ C.caps) a x → dom x ≠ d0 := by
    intro x hx
    induction hx with
    | refl => exact hda
    | tail _ h₂ ih =>
        have hedge := names_only_permitted C dom policy hwi _ _ h₂
        intro hc
        have hfalse := (hiso _ ih).2
        rw [hc] at hedge
        rw [hedge] at hfalse
        exact Bool.noConfusion hfalse
  exact key b hreach hdb

/-! ## Non-vacuity: a concrete microkit-style system

A realistic static layout with three protection domains that must be isolated,
sharing only through a dedicated endpoint channel:

* driver domain  (`= 10`): driver TCB (`1`) and its private frame (`2`)
* app domain     (`= 20`): app TCB (`4`) and its private frame (`5`)
* endpoint channel domain (`= 40`): the shared endpoint object (`3`)
* secret domain  (`= 30`): a confidential object (`6`), fully isolated

The policy lets the driver and the app each talk to the endpoint channel, but
*not* to one another directly, and lets *nobody* touch the secret domain. -/

/-- Protection-domain assignment for the concrete system. -/
def dom : Obj → ℕ := fun o =>
  if o = 1 then 10       -- driver TCB
  else if o = 2 then 10  -- driver private frame
  else if o = 3 then 40  -- shared endpoint (its own channel domain)
  else if o = 4 then 20  -- app TCB
  else if o = 5 then 20  -- app private frame
  else if o = 6 then 30  -- secret object
  else 0

/-- Domain-connection policy.  Reflexive (a domain always connects to itself);
    driver(10) ↔ endpoint(40) and app(20) ↔ endpoint(40) are permitted; the
    driver and the app are *not* directly connected; the secret domain(30) is
    connected to no other domain. -/
def policy : ℕ → ℕ → Bool := fun d1 d2 =>
  if d1 = d2 then true
  else if d1 = 10 ∧ d2 = 40 then true
  else if d1 = 40 ∧ d2 = 10 then true
  else if d1 = 20 ∧ d2 = 40 then true
  else if d1 = 40 ∧ d2 = 20 then true
  else false

/-- The **well-wired** spec: driver and app touch only their own frames and the
    shared endpoint. -/
def goodSys : CapDL where
  objs := {1, 2, 3, 4, 5, 6}
  caps := {(1, 2), (1, 3), (4, 3), (4, 5)}

/-- The **mis-wired** spec: identical to `goodSys` but with a stray capability
    `(4, 2)` — the app TCB directly names the driver's private frame, an
    isolation violation the domain policy forbids. -/
def badSys : CapDL where
  objs := {1, 2, 3, 4, 5, 6}
  caps := {(1, 2), (1, 3), (4, 3), (4, 5), (4, 2)}

/-- (a) The well-wired spec **passes** the checker: `checkIsolation` certifies it. -/
theorem goodSys_passes : checkIsolation goodSys dom policy = true := by decide

/-- (b) The mis-wired spec is **rejected**: the checker catches the stray
    app→driver-frame capability. -/
theorem badSys_rejected : checkIsolation badSys dom policy = false := by decide

/-- The certificate, transported through soundness: `goodSys` is well-isolated. -/
theorem goodSys_wellIsolated : WellIsolated goodSys dom policy :=
  (checkIsolation_correct goodSys dom policy).mp goodSys_passes

/-- The secret domain (`30`) is fully isolated under `policy`. -/
theorem secret_isolated (d : ℕ) (hd : d ≠ 30) :
    policy 30 d = false ∧ policy d 30 = false := by
  constructor
  · unfold policy
    split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; omega)
  · unfold policy
    split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; omega)

/-- (c) **Transitive isolation, instantiated.**  In the well-wired spec the app
    domain can never reach the secret object through *any* chain of capabilities. -/
theorem secret_unreachable_from_app : ¬ Reaches goodSys 4 6 :=
  isolated_domain_unreachable_into goodSys dom policy goodSys_wellIsolated 30
    secret_isolated 4 6 (by decide) (by decide)

/-- And dually, the secret object can never reach out into the app domain. -/
theorem secret_cannot_reach_app : ¬ Reaches goodSys 6 4 :=
  isolated_domain_unreachable goodSys dom policy goodSys_wellIsolated 30
    secret_isolated 6 4 (by decide) (by decide)

end Brockian.HighAssurance.CapDLIsolation
