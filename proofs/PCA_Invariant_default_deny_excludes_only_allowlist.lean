import Mathlib

/-!
# Proof-Carrying Apps — AccessPolicy invariants (`PCA.Invariant` namespace)

Category: Proof-Carrying Apps
Provenance: Aristotle theorem prover (Harmonic); assembled from two AXLE-verified
best-proof files into one registered module.

The two developments each introduced a helper `PCA.AccessPolicy` with a *different*
signature (an allowlist vs. a row-level-security permission relation), which
cannot coexist in one namespace.  The default-deny model keeps its `PCA.AccessPolicy`
verbatim (its target statement names `AccessPolicy`).  The row-level-security model is
placed under `PCA.Invariant` with its helper structure renamed
`AccessPolicy → RowPolicy`; its target statement `rls_off_implies_no_row_protection`
never mentions that helper by name, so it is preserved verbatim.
-/

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Default deny -/

namespace PCA

/-- The verdict returned by the isolation engine for a single request. -/
inductive Verdict
  | allow
  | deny
  deriving DecidableEq, Repr

/-- A default-deny policy for requests of type `Req` is given by its allowlist:
the set of requests that are explicitly permitted. Everything else is denied. -/
structure AccessPolicy (Req : Type*) where
  /-- The set of explicitly permitted requests. -/
  allowlist : Set Req

variable {Req : Type*}

/-- The isolation engine's decision procedure: a request is allowed exactly when it
appears on the allowlist, and is denied otherwise (default deny). -/
noncomputable def AccessPolicy.eval (P : AccessPolicy Req) (r : Req) : Verdict :=
  if r ∈ P.allowlist then Verdict.allow else Verdict.deny

/-- The set of requests the engine permits. -/
def AccessPolicy.permitted (P : AccessPolicy Req) : Set Req := {r | P.eval r = Verdict.allow}

/-- The set of requests the engine blocks. -/
def AccessPolicy.blocked (P : AccessPolicy Req) : Set Req := {r | P.eval r = Verdict.deny}

@[simp]
theorem AccessPolicy.eval_eq_allow_iff (P : AccessPolicy Req) (r : Req) :
    P.eval r = Verdict.allow ↔ r ∈ P.allowlist := by
  unfold AccessPolicy.eval
  split <;> simp_all

@[simp]
theorem AccessPolicy.eval_eq_deny_iff (P : AccessPolicy Req) (r : Req) :
    P.eval r = Verdict.deny ↔ r ∉ P.allowlist := by
  unfold AccessPolicy.eval
  split <;> simp_all

namespace Invariant

/-- **Soundness of default deny**: everything the engine permits is on the allowlist. -/
theorem permitted_subset_allowlist (P : AccessPolicy Req) : P.permitted ⊆ P.allowlist := by
  intro r hr
  simpa [AccessPolicy.permitted] using hr

/-- **Completeness of default deny**: everything on the allowlist is permitted. -/
theorem allowlist_subset_permitted (P : AccessPolicy Req) : P.allowlist ⊆ P.permitted := by
  intro r hr
  simpa [AccessPolicy.permitted] using hr

/-- The permitted set is exactly the allowlist. -/
theorem permitted_eq_allowlist (P : AccessPolicy Req) : P.permitted = P.allowlist :=
  Set.Subset.antisymm (permitted_subset_allowlist P) (allowlist_subset_permitted P)

/-- **Default deny excludes only the allowlist**: under a default-deny policy, the set of
requests blocked by the isolation engine is exactly the complement of the allowlist.
Equivalently, the engine denies every request except those explicitly permitted, and it
denies no request that is explicitly permitted. -/
theorem default_deny_excludes_only_allowlist (P : AccessPolicy Req) :
    P.blocked = (P.allowlist)ᶜ := by
  have h : P.blocked = {r : Req | ¬ r ∈ P.allowlist} := by
    simp [AccessPolicy.blocked]
  rw [h, ← Set.compl_setOf, Set.setOf_mem_eq]

/-- Restatement: a request is blocked iff it is not on the allowlist. -/
theorem mem_blocked_iff (P : AccessPolicy Req) (r : Req) : r ∈ P.blocked ↔ r ∉ P.allowlist := by
  rw [default_deny_excludes_only_allowlist]
  exact Set.mem_compl_iff _ _

/-- No request is both permitted and blocked. -/
theorem permitted_disjoint_blocked (P : AccessPolicy Req) : Disjoint P.permitted P.blocked := by
  rw [permitted_eq_allowlist, default_deny_excludes_only_allowlist]
  exact disjoint_compl_right

/-- Every request is either permitted or blocked. -/
theorem permitted_union_blocked (P : AccessPolicy Req) : P.permitted ∪ P.blocked = Set.univ := by
  rw [permitted_eq_allowlist, default_deny_excludes_only_allowlist]
  exact Set.union_compl_self _

/-- The empty allowlist blocks everything: pure default deny. -/
theorem blocked_of_empty_allowlist (P : AccessPolicy Req) (h : P.allowlist = ∅) :
    P.blocked = Set.univ := by
  rw [default_deny_excludes_only_allowlist, h, Set.compl_empty]

end Invariant

end PCA

/-! ## Row-level security -/

namespace PCA.Invariant

/-- A row-level security policy: it says which principals are permitted to see which rows.
(Renamed from the source's `AccessPolicy` to avoid a collision with the default-deny `PCA.AccessPolicy`.) -/
structure RowPolicy (Principal Row : Type*) where
  /-- `permits p r` holds when the policy grants principal `p` access to row `r`. -/
  permits : Principal → Row → Prop

/-- A table of the isolation engine's model: a row-level-security (RLS) switch together with
the list of policies that are consulted when the switch is on. -/
structure Table (Principal Row : Type*) where
  /-- Whether row-level security is enabled for this table. -/
  rlsEnabled : Bool
  /-- The policies attached to the table (only consulted when `rlsEnabled = true`). -/
  policies : List (RowPolicy Principal Row)

variable {Principal Row : Type*}

/-- Access semantics of the engine: when RLS is off every row is visible to every principal;
when RLS is on a row is visible only if some attached policy permits it. -/
def Table.Visible (t : Table Principal Row) (p : Principal) (r : Row) : Prop :=
  t.rlsEnabled = false ∨ ∃ pol ∈ t.policies, pol.permits p r

/-- A row is *protected* when at least one principal is denied access to it. -/
def Table.RowProtected (t : Table Principal Row) (r : Row) : Prop :=
  ∃ p : Principal, ¬ t.Visible p r

/-- The set of rows that enjoy some protection. -/
def Table.protectedRows (t : Table Principal Row) : Set Row :=
  {r | t.RowProtected r}

/-- **Main invariant.** If row-level security is switched off on a table, then no row of that
table is protected: every principal can see every row. -/
theorem rls_off_implies_no_row_protection
    (t : Table Principal Row) (h : t.rlsEnabled = false) :
    ∀ r : Row, ¬ t.RowProtected r := by
  rintro r ⟨p, hp⟩
  exact hp (Or.inl h)

/-- Equivalent phrasing: with RLS off the set of protected rows is empty. -/
theorem protectedRows_eq_empty_of_rls_off
    (t : Table Principal Row) (h : t.rlsEnabled = false) :
    t.protectedRows = (∅ : Set Row) := by
  ext r
  simpa [Table.protectedRows] using rls_off_implies_no_row_protection t h r

/-- Equivalent phrasing: with RLS off, every principal sees every row. -/
theorem visible_of_rls_off
    (t : Table Principal Row) (h : t.rlsEnabled = false) (p : Principal) (r : Row) :
    t.Visible p r :=
  Or.inl h

/-- Converse (completeness of the invariant): if some row is protected, RLS must be on. -/
theorem rls_on_of_row_protected
    (t : Table Principal Row) {r : Row} (h : t.RowProtected r) :
    t.rlsEnabled = true := by
  rcases h with ⟨p, hp⟩
  cases hb : t.rlsEnabled with
  | false => exact absurd (Or.inl hb) hp
  | true => rfl

/-- Exact characterisation of protection in the model: a row is protected precisely when RLS is
on and some principal is permitted by none of the attached policies. -/
theorem rowProtected_iff (t : Table Principal Row) (r : Row) :
    t.RowProtected r ↔
      t.rlsEnabled = true ∧ ∃ p : Principal, ∀ pol ∈ t.policies, ¬ pol.permits p r := by
  constructor
  · intro h
    refine ⟨rls_on_of_row_protected t h, ?_⟩
    rcases h with ⟨p, hp⟩
    exact ⟨p, fun pol hpol hperm => hp (Or.inr ⟨pol, hpol, hperm⟩)⟩
  · rintro ⟨hon, p, hp⟩
    refine ⟨p, ?_⟩
    rintro (hoff | ⟨pol, hpol, hperm⟩)
    · exact absurd (hon.symm.trans hoff) (by simp)
    · exact hp pol hpol hperm

/-- Switching RLS off on any table wipes out all row protection. -/
theorem protectedRows_disableRls_eq_empty (t : Table Principal Row) :
    ({t with rlsEnabled := false} : Table Principal Row).protectedRows = (∅ : Set Row) :=
  protectedRows_eq_empty_of_rls_off _ rfl

/-- The invariant is not vacuous: with RLS *on* and no permitting policy, a row really is
protected. -/
theorem exists_rowProtected_of_rls_on :
    ∃ t : Table Bool Unit, t.rlsEnabled = true ∧ t.RowProtected () := by
  refine ⟨⟨true, []⟩, rfl, ?_⟩
  exact (rowProtected_iff _ ()).2 ⟨rfl, true, by simp⟩

end PCA.Invariant
