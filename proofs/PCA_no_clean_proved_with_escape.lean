import Mathlib

/-!
# Proof-Carrying Apps — Core access-control model (bare `PCA` namespace)

Category: Proof-Carrying Apps
Provenance: Aristotle theorem prover (Harmonic); assembled from individual
AXLE-verified best-proof files into one registered module.

A capability-based access-control model: a caller `c` may access a resource `r`
when `r` is in `c`'s scope, or `c` is privileged, or `r` is unowned.  The shared
`canAccess` predicate is declared once; every theorem below is stated verbatim
from its source file against that predicate.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

variable {P R : Type}

/-- A caller `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **Default deny**: with an empty scope relation and no escape hatches
(no privileged clients, no unowned resources), nothing is accessible. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    {c : P} {r : R} (hscope : ∀ c r, ¬ inScope c r) (hpriv : ∀ c, ¬ isPriv c)
    (hown : ∀ r, ¬ isUnowned r) : ¬ canAccess inScope isPriv isUnowned c r :=
  not_or.mpr ⟨hscope c r, not_or.mpr ⟨hpriv c, hown r⟩⟩

/-- Adding escape hatches (privilege, unowned resources) only enlarges access:
being in scope already suffices for access. -/
theorem escape_monotone (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : inScope c r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inl h

/-- `canAccess` is monotone in each of its three policy predicates: weakening the
scope relation, or the privilege / unowned predicates, only enlarges access. -/
theorem canAccess_mono {inScope inScope' : P → R → Prop} {isPriv isPriv' : P → Prop}
    {isUnowned isUnowned' : R → Prop}
    (hs : ∀ c r, inScope c r → inScope' c r) (hp : ∀ c, isPriv c → isPriv' c)
    (hu : ∀ r, isUnowned r → isUnowned' r) (c : P) (r : R)
    (h : canAccess inScope isPriv isUnowned c r) :
    canAccess inScope' isPriv' isUnowned' c r :=
  h.imp (hs c r) (Or.imp (hp c) (hu r))

/-- Out of scope, access holds iff some escape hatch fires. -/
theorem leak_iff_escape_when_out_of_scope
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) := by
  constructor
  · rintro (hs | he)
    · exact absurd hs h
    · exact he
  · intro he
    exact Or.inr he

/-- With no privileged capabilities and no unowned resources, any granted access
is in-scope. -/
theorem no_escape_no_leak {isPriv : P → Prop} {isUnowned : R → Prop}
    (inScope : P → R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (hpriv c)
  · exact absurd h (hunowned r)

/-- Owner-equality scope with no escapes is isolated: access implies ownership. -/
theorem owner_only_isolated (ownerOf : R → P) (c : P) (r : R)
    (h : canAccess (fun c r => ownerOf r = c) (fun _ => False) (fun _ => False) c r) :
    ownerOf r = c := by
  rcases h with h | h | h
  · exact h
  · exact h.elim
  · exact h.elim

/-- A privileged caller always has access (models the admin bypass). -/
theorem priv_is_escape (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : isPriv c) : canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inl h)

/-- Removing the "unowned" disjunct tightens the policy: any access permitted by
the tightened policy is also permitted by the original policy. -/
theorem tightening_refines (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    canAccess inScope isPriv (fun _ => False) c r →
      canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact h.elim

/-- Any caller can reach an unowned row: this models the `IS NULL` hole in the
access-control predicate. -/
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

/-- A `WITH CHECK true` write policy admits every principal/row pair: with
`canWrite := fun _ _ => True`, every principal may write every row, so the
policy models "forge any row". -/
theorem with_check_true_admits_forge
    (canWrite : P → R → Prop) (hcanWrite : canWrite = fun (_ : P) (_ : R) => True) :
    ∀ (c : P) (r : R), canWrite c r := by
  subst hcanWrite
  intro c r
  trivial

/-- Soundness-fuzz invariant: a clean-isolation proof (every access is in scope)
is incompatible with an escape firing out of scope. -/
theorem no_clean_proved_with_escape
    {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hclean : ∀ c r, canAccess inScope isPriv isUnowned c r → inScope c r)
    (hescape : ∃ c r, ¬ inScope c r ∧ (isPriv c ∨ isUnowned r)) : False := by
  obtain ⟨c, r, hns, hesc⟩ := hescape
  exact hns (hclean c r (Or.inr hesc))

end PCA
