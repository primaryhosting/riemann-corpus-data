/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- A configuration of the isolation engine: a domain identifier together with the
privilege level currently held in that domain. -/
structure Config where
  /-- The isolation domain (e.g. a sandbox / process identifier). -/
  dom : Nat
  /-- The privilege level held in this configuration. -/
  priv : Nat
  deriving DecidableEq

/-- A policy is the one-step transition relation permitted by the isolation engine. -/
def Policy : Type := Config → Config → Prop

/-- `Q` is at least as permissive as `P`. -/
def Weaker (P Q : Policy) : Prop := ∀ a b : Config, P a b → Q a b

/-- Multi-step reachability under a policy. -/
inductive Reach (P : Policy) : Config → Config → Prop
  | refl (c : Config) : Reach P c c
  | step {a b c : Config} : Reach P a b → P b c → Reach P a c

/-- A privilege escape from `c`: some configuration with strictly higher privilege
than `c` is reachable from `c`. -/
def Escapes (P : Policy) (c : Config) : Prop :=
  ∃ d : Config, Reach P c d ∧ c.priv < d.priv

/-- Reachability is monotone in the policy. -/
theorem reach_monotone {P Q : Policy} (hPQ : Weaker P Q) {a b : Config}
    (h : Reach P a b) : Reach Q a b := by
  induction h with
  | refl => exact Reach.refl _
  | step _ hstep ih => exact Reach.step ih (hPQ _ _ hstep)

/-- **Privilege escape is monotone in the policy**: weakening the policy can only
create escapes, never remove them. -/
theorem priv_escape_monotone {P Q : Policy} (hPQ : Weaker P Q) {c : Config}
    (h : Escapes P c) : Escapes Q c := by
  obtain ⟨d, hreach, hlt⟩ := h
  exact ⟨d, reach_monotone hPQ hreach, hlt⟩

/-- Under a non-escalating policy, every reachable configuration has privilege at most
that of the starting configuration. -/
theorem priv_le_of_reach {P : Policy} (hP : ∀ a b : Config, P a b → b.priv ≤ a.priv)
    {a b : Config} (h : Reach P a b) : b.priv ≤ a.priv := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hstep ih => exact Nat.le_trans (hP _ _ hstep) ih

/-- Soundness of the isolation model: a non-escalating policy admits no privilege escape. -/
theorem no_escape_of_nonescalating {P : Policy}
    (hP : ∀ a b : Config, P a b → b.priv ≤ a.priv) (c : Config) : ¬ Escapes P c := by
  rintro ⟨d, hreach, hlt⟩
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (priv_le_of_reach hP hreach))

/-- Completeness of the isolation model: if no configuration admits a privilege escape,
then the policy is non-escalating. -/
theorem nonescalating_of_no_escape {P : Policy} (h : ∀ c : Config, ¬ Escapes P c)
    (a b : Config) (hab : P a b) : b.priv ≤ a.priv := by
  rcases Nat.lt_or_ge a.priv b.priv with hlt | hge
  · exact absurd ⟨b, Reach.step (Reach.refl a) hab, hlt⟩ (h a)
  · exact hge

/-- Soundness and completeness combined: the isolation engine's model is escape-free
exactly when its policy never escalates privilege. -/
theorem no_escape_iff_nonescalating {P : Policy} :
    (∀ c : Config, ¬ Escapes P c) ↔ (∀ a b : Config, P a b → b.priv ≤ a.priv) :=
  ⟨fun h => nonescalating_of_no_escape h, fun h => no_escape_of_nonescalating h⟩

end PCA.Isolation

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

