import Mathlib

/-!
# Proof-Carrying Apps — Write Integrity (`PCA.WriteIntegrity` namespace)

Category: Proof-Carrying Apps
Provenance: Aristotle theorem prover (Harmonic); assembled from two AXLE-verified
best-proof files into one registered module.  The two developments use disjoint
helper models (a multi-tenant store reference monitor, and a capability-token
write checker), so they coexist unchanged in one namespace.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.WriteIntegrity

/-! ## Multi-tenant store reference monitor

A multi-tenant store maps resource identifiers to records.  Every stored record
carries the tenant that owns it together with a payload.  A write request names
a principal, a resource, the tenant under which the principal claims to act, and
the payload to be stored.

The *reference monitor* accepts a request only when

* the principal is a member of the tenant it claims to act for, and
* if the resource already exists, it is owned by exactly that tenant.
-/

universe u v w z

variable {Res : Type u} {Tenant : Type v} {Prin : Type w} {Val : Type z}

/-- A stored record: the owning tenant together with the payload. -/
structure Record (Tenant : Type v) (Val : Type z) where
  /-- The tenant owning the record. -/
  tenant : Tenant
  /-- The stored payload. -/
  value : Val

/-- A store maps resource identifiers to records (`none` = the resource is absent). -/
abbrev Store (Res : Type u) (Tenant : Type v) (Val : Type z) := Res → Option (Record Tenant Val)

/-- A write request. -/
structure WriteReq (Res : Type u) (Tenant : Type v) (Prin : Type w) (Val : Type z) where
  /-- The principal issuing the write. -/
  principal : Prin
  /-- The tenant the principal claims to act for. -/
  tenant : Tenant
  /-- The resource to be written. -/
  resource : Res
  /-- The payload to be written. -/
  value : Val

/-- The membership relation of the isolation engine: `mem p t` means principal
`p` belongs to tenant `t`. -/
abbrev Memberships (Prin : Type w) (Tenant : Type v) := Prin → Tenant → Prop

/-- Pointwise update of a store at a single resource. -/
def upd [DecidableEq Res] (st : Store Res Tenant Val) (x : Res)
    (v : Option (Record Tenant Val)) : Store Res Tenant Val :=
  fun y => if y = x then v else st y

@[simp] theorem upd_self [DecidableEq Res] (st : Store Res Tenant Val) (x : Res)
    (v : Option (Record Tenant Val)) : upd st x v x = v := by
  simp [upd]

theorem upd_of_ne [DecidableEq Res] (st : Store Res Tenant Val) (x y : Res)
    (v : Option (Record Tenant Val)) (h : y ≠ x) : upd st x v y = st y := by
  simp [upd, h]

/-- The reference monitor's decision: the principal must be a member of the
claimed tenant, and an already existing resource must belong to that tenant. -/
def Authorized (mem : Memberships Prin Tenant) (st : Store Res Tenant Val)
    (r : WriteReq Res Tenant Prin Val) : Prop :=
  mem r.principal r.tenant ∧ ∀ rec, st r.resource = some rec → rec.tenant = r.tenant

/-- The raw (unguarded) effect of a write request on the store. -/
def rawWrite [DecidableEq Res] (st : Store Res Tenant Val)
    (r : WriteReq Res Tenant Prin Val) : Store Res Tenant Val :=
  upd st r.resource (some ⟨r.tenant, r.value⟩)

/-- One step of the guarded engine: perform the write only if it is authorized,
otherwise leave the store untouched. -/
noncomputable def step [DecidableEq Res] (mem : Memberships Prin Tenant)
    (st : Store Res Tenant Val) (r : WriteReq Res Tenant Prin Val) : Store Res Tenant Val :=
  open Classical in
  if Authorized mem st r then rawWrite st r else st

/-- A resource is *foreign* to a principal when it currently stores a record
owned by a tenant the principal is not a member of. -/
def Foreign (mem : Memberships Prin Tenant) (st : Store Res Tenant Val)
    (p : Prin) (x : Res) : Prop :=
  ∃ rec, st x = some rec ∧ ¬ mem p rec.tenant

/-- **Member check prevents cross-tenant writes.**

If the reference monitor's membership check is in force, then a single guarded
step never alters any resource that is foreign to the acting principal: the
store's contents at such a resource are exactly what they were before. -/
theorem member_check_prevents_cross_tenant_write [DecidableEq Res]
    (mem : Memberships Prin Tenant) (st : Store Res Tenant Val)
    (r : WriteReq Res Tenant Prin Val) (x : Res)
    (hx : Foreign mem st r.principal x) :
    step mem st r x = st x := by
  obtain ⟨rec, hrec, hnot⟩ := hx
  unfold step
  split
  · rename_i hauth
    obtain ⟨hmem, howner⟩ := hauth
    have hne : x ≠ r.resource := by
      rintro rfl
      exact hnot ((howner rec hrec) ▸ hmem)
    exact upd_of_ne st r.resource x _ hne
  · rfl

/-- The record stored at a foreign resource is unchanged by a guarded step. -/
theorem foreign_owner_stable [DecidableEq Res]
    (mem : Memberships Prin Tenant) (st : Store Res Tenant Val)
    (r : WriteReq Res Tenant Prin Val) (x : Res) (rec : Record Tenant Val)
    (hrec : st x = some rec) (hnot : ¬ mem r.principal rec.tenant) :
    step mem st r x = some rec := by
  rw [member_check_prevents_cross_tenant_write mem st r x ⟨rec, hrec, hnot⟩]
  exact hrec

/-- Iterating guarded steps with arbitrary requests still cannot change a
resource, as long as it is foreign to each acting principal along the way. -/
theorem foldl_step_preserves_foreign [DecidableEq Res]
    (mem : Memberships Prin Tenant) (x : Res) (rec : Record Tenant Val) :
    ∀ (rs : List (WriteReq Res Tenant Prin Val)) (st : Store Res Tenant Val),
      st x = some rec → (∀ r ∈ rs, ¬ mem r.principal rec.tenant) →
      (rs.foldl (step mem) st) x = some rec := by
  intro rs
  induction rs with
  | nil => intro st h _; simpa using h
  | cons r rs ih =>
      intro st h hall
      refine ih (step mem st r) ?_ (fun q hq => hall q (List.mem_cons_of_mem _ hq))
      exact foreign_owner_stable mem st r x rec h (hall r (List.mem_cons_self ..))

/-- Authorized writes do take effect: the guard is not vacuously restrictive. -/
theorem step_of_authorized [DecidableEq Res]
    (mem : Memberships Prin Tenant) (st : Store Res Tenant Val)
    (r : WriteReq Res Tenant Prin Val) (h : Authorized mem st r) :
    step mem st r r.resource = some ⟨r.tenant, r.value⟩ := by
  unfold step
  split
  · simp [rawWrite]
  · exact absurd h (by assumption)

/-- Sharpness: without the membership check the write really can clobber a
record owned by another tenant.  Here principal `0` is a member only of tenant
`0`, yet the raw write overwrites the resource owned by tenant `1`. -/
theorem rawWrite_can_cross_tenant :
    ∃ (mem : Memberships Nat Nat) (st : Store Nat Nat Nat) (r : WriteReq Nat Nat Nat Nat)
      (x : Nat), Foreign mem st r.principal x ∧ rawWrite st r x ≠ st x := by
  refine ⟨fun p t => p = t, fun _ => some ⟨1, 0⟩,
    { principal := 0, tenant := 0, resource := 0, value := 0 }, 0, ⟨⟨1, 0⟩, rfl, by simp⟩, ?_⟩
  simp [rawWrite, upd, Record.mk.injEq]

/-! ## Capability-token write checker

A separate, self-contained model of a write checker: a write request targets a
memory region, carries a payload, and presents a capability certificate that is
supposed to witness the writer's authority over that region. -/

/-- A write request submitted to the isolation engine: it targets a memory `region`,
carries a `payload`, and presents a capability certificate `cert` that is supposed to
witness the writer's authority over that region. -/
structure Write where
  region : Nat
  payload : Nat
  cert : Nat
  deriving DecidableEq

/-- `key r` is the capability token authorizing writes to region `r`.
A write is *authentic* exactly when the certificate it presents is the region's token. -/
def Authentic (key : Nat → Nat) (w : Write) : Prop := w.cert = key w.region

instance (key : Nat → Nat) (w : Write) : Decidable (Authentic key w) := by
  unfold Authentic; infer_instance

/-- The engine's admission relation: a write is let through exactly when the runtime
`check` accepts it. -/
def Admits (check : Write → Bool) (w : Write) : Prop := check w = true

/-- Write integrity (soundness of the engine's `check`): every admitted write is authentic. -/
def Sound (key : Nat → Nat) (check : Write → Bool) : Prop :=
  ∀ w : Write, Admits check w → Authentic key w

/-- A *forgery* against a checker: a write that the engine admits although it is not
authentic. -/
def Forges (key : Nat → Nat) (check : Write → Bool) (w : Write) : Prop :=
  Admits check w ∧ ¬ Authentic key w

/-- **With a trivially-true check, the engine admits a forgery.**

If the isolation engine's write check is the constant `true` predicate, then for *any*
capability assignment `key` there is a write that is admitted yet carries a bogus
certificate; consequently the engine's write-integrity property `Sound` fails.

Interpretation: an always-accepting check discharges no proof obligation, so the
proof-carrying discipline degenerates and write integrity is lost. -/
theorem with_check_true_admits_forge (key : Nat → Nat) :
    (∃ w : Write, Forges key (fun _ => true) w) ∧ ¬ Sound key (fun _ => true) := by
  have hforge : Forges key (fun _ => true) ⟨0, 0, key 0 + 1⟩ := by
    refine ⟨rfl, ?_⟩
    intro h
    simp only [Authentic] at h
    omega
  refine ⟨⟨_, hforge⟩, ?_⟩
  intro hs
  exact hforge.2 (hs _ hforge.1)

end PCA.WriteIntegrity
