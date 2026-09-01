/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires every `import` command to precede all other
commands in a file, so no `import Mathlib` line may appear after the module
docstring above.  The development below is therefore self-contained in core
Lean 4; the sets of the model are represented as predicates `R → Prop`, which
is exactly Mathlib's `Set R` unfolded (`Set.ext` / `Set.mem_compl_iff`
correspond here to `funext`/`propext` and `PCA.Policy.decide_eq_deny_iff`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

universe u

/-- The outcome of consulting the isolation engine on a request. -/
inductive Decision
  | allow : Decision
  | deny : Decision
  deriving DecidableEq, Repr

/-- A collection of requests, i.e. a set of `R` represented as a predicate. -/
def Requests (R : Type u) : Type u := R → Prop

/-- Membership in a collection of requests. -/
def Requests.mem {R : Type u} (S : Requests R) (r : R) : Prop := S r

/-- Complement of a collection of requests. -/
def Requests.compl {R : Type u} (S : Requests R) : Requests R := fun r => ¬ S r

/-- Union of two collections of requests. -/
def Requests.union {R : Type u} (S T : Requests R) : Requests R := fun r => S r ∨ T r

/-- Intersection of two collections of requests. -/
def Requests.inter {R : Type u} (S T : Requests R) : Requests R := fun r => S r ∧ T r

/-- The empty collection of requests. -/
def Requests.empty (R : Type u) : Requests R := fun _ => False

/-- The collection of all requests. -/
def Requests.univ (R : Type u) : Requests R := fun _ => True

/-- A *default-deny* policy for requests of type `R`: it carries an allowlist,
and everything not on that allowlist is denied. -/
structure Policy (R : Type u) where
  /-- The set of explicitly allowed requests. -/
  allowlist : Requests R

variable {R : Type u} (P : Policy R) (r : R)

open Classical in
/-- The decision procedure of a default-deny policy: allow exactly the requests
on the allowlist, deny everything else. -/
noncomputable def Policy.decide : Decision :=
  if P.allowlist r then Decision.allow else Decision.deny

/-- The collection of requests the engine actually permits. -/
noncomputable def Policy.permitted : Requests R := fun x => P.decide x = Decision.allow

/-- The collection of requests the engine actually denies. -/
noncomputable def Policy.denied : Requests R := fun x => P.decide x = Decision.deny

/-- Soundness of the allow decision: a request is permitted exactly when it is
on the allowlist. -/
theorem Policy.decide_eq_allow_iff : P.decide r = Decision.allow ↔ P.allowlist r := by
  unfold Policy.decide
  by_cases h : P.allowlist r
  · simp [h]
  · simp [h]

/-- A request is denied exactly when it is not on the allowlist. -/
theorem Policy.decide_eq_deny_iff : P.decide r = Decision.deny ↔ ¬ P.allowlist r := by
  unfold Policy.decide
  by_cases h : P.allowlist r
  · simp [h]
  · simp [h]

/-- Every request receives exactly one of the two decisions. -/
theorem Policy.decide_allow_or_deny :
    P.decide r = Decision.allow ∨ P.decide r = Decision.deny := by
  unfold Policy.decide
  by_cases h : P.allowlist r
  · simp [h]
  · simp [h]

namespace Invariant

/-- **Default deny excludes only the allowlist.**

For a default-deny isolation policy, the collection of denied requests is
exactly the complement of the allowlist: nothing on the allowlist is denied
(soundness) and everything off the allowlist is denied (completeness). -/
theorem default_deny_excludes_only_allowlist {R : Type u} (P : Policy R) :
    P.denied = P.allowlist.compl := by
  funext x
  exact propext (P.decide_eq_deny_iff x)

/-- Dual form: the permitted collection is exactly the allowlist. -/
theorem default_deny_permits_exactly_allowlist {R : Type u} (P : Policy R) :
    P.permitted = P.allowlist := by
  funext x
  exact propext (P.decide_eq_allow_iff x)

/-- The permitted and denied collections cover the whole request space. -/
theorem permitted_union_denied {R : Type u} (P : Policy R) :
    P.permitted.union P.denied = Requests.univ R := by
  funext x
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  exact P.decide_allow_or_deny x

/-- No request is both permitted and denied. -/
theorem permitted_inter_denied {R : Type u} (P : Policy R) :
    P.permitted.inter P.denied = Requests.empty R := by
  funext x
  refine propext ⟨fun h => ?_, fun h => h.elim⟩
  have h1 : P.decide x = Decision.allow := h.1
  have h2 : P.decide x = Decision.deny := h.2
  rw [h1] at h2
  exact Decision.noConfusion h2

/-- With an empty allowlist, everything is denied: the engine is closed by default. -/
theorem denied_of_empty_allowlist {R : Type u} (P : Policy R)
    (h : P.allowlist = Requests.empty R) :
    P.denied = Requests.univ R := by
  rw [default_deny_excludes_only_allowlist, h]
  funext x
  exact propext ⟨fun _ => trivial, fun _ hx => hx.elim⟩

end Invariant

end PCA

#print axioms PCA.Invariant.default_deny_excludes_only_allowlist

