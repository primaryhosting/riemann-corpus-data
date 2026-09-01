/-!
# In Scope Encoding Sound
Category: Proof-Carrying Apps
Target: PCA.Isolation.in_scope_encoding_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-- A resource is identified by a hierarchical path: a list of name segments,
read from the root downwards. -/
abbrev Path := List String

/-- The isolation policy of a sandboxed app: a list of granted subtrees
(`roots`) together with a list of explicitly revoked subtrees (`denied`). -/
structure Scope where
  /-- Subtrees the app has been granted access to. -/
  roots : List Path
  /-- Subtrees carved out of the grants; denial takes precedence. -/
  denied : List Path
  deriving Repr

/-- Declarative semantics of the isolation engine: a resource `p` lies in the
scope `s` when some granted root is an ancestor of (or equal to) `p`, and no
denied subtree is an ancestor of (or equal to) `p`. -/
def InScope (s : Scope) (p : Path) : Prop :=
  (∃ r ∈ s.roots, r <+: p) ∧ ∀ d ∈ s.denied, ¬ d <+: p

/-- The executable encoding of the scope check used by the isolation engine. -/
def encodeInScope (s : Scope) (p : Path) : Bool :=
  s.roots.any (fun r => r.isPrefixOf p) && !s.denied.any (fun d => d.isPrefixOf p)

/-- **Soundness and completeness of the `in scope` encoding.**
The boolean decision procedure `encodeInScope` returns `true` on exactly those
resource paths that the declarative isolation model `InScope` admits. -/
theorem in_scope_encoding_sound (s : Scope) (p : Path) :
    encodeInScope s p = true ↔ InScope s p := by
  unfold encodeInScope InScope
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.any_eq_false, List.isPrefixOf_iff_prefix]

/-- Decidability of the declarative model, transported along the encoding. -/
instance instDecidableInScope (s : Scope) (p : Path) : Decidable (InScope s p) :=
  decidable_of_iff _ (in_scope_encoding_sound s p)

/-- Denial always wins: a path lying under a denied subtree is never in scope. -/
theorem not_inScope_of_denied {s : Scope} {p : Path} {d : Path}
    (hd : d ∈ s.denied) (hdp : d <+: p) : ¬ InScope s p := by
  rintro ⟨-, h⟩
  exact h d hd hdp

/-- Scopes are closed downwards along the resource hierarchy in the following
sense: extending an in-scope path keeps it inside every granted root, so it can
only leave the scope by hitting an explicit denial. -/
theorem inScope_append {s : Scope} {p q : Path} (hp : InScope s p)
    (hq : ∀ d ∈ s.denied, ¬ d <+: (p ++ q)) : InScope s (p ++ q) := by
  obtain ⟨⟨r, hr, hrp⟩, -⟩ := hp
  exact ⟨⟨r, hr, hrp.trans (List.prefix_append p q)⟩, hq⟩

/-- An empty grant list isolates the app completely. -/
theorem not_inScope_of_no_roots {s : Scope} (h : s.roots = []) (p : Path) :
    ¬ InScope s p := by
  rintro ⟨⟨r, hr, -⟩, -⟩
  rw [h] at hr
  exact absurd hr (List.not_mem_nil)

end Isolation
end PCA

section AxiomAudit
open PCA.Isolation
#print axioms PCA.Isolation.in_scope_encoding_sound
end AxiomAudit

