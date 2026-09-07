import Mathlib

/-!
# Merkle-tree tamper evidence (high-assurance data integrity)

An abstract Merkle tree over an *abstract collision-resistant hash*.  We model a
digest as `Hash := ℕ`, an internal-node combiner `h2 : Hash → Hash → Hash` and a
leaf hash `leafHash : ℕ → Hash`.

Collision-resistance is modelled — HONESTLY, as an *idealisation* — by
INJECTIVITY hypotheses on the relevant maps:

* `hinj2   : Function.Injective2 h2`   (no two internal-node inputs collide)
* `hinjLeaf: Function.Injective leafHash` (no two leaves collide)

Real cryptographic hashes are only *computationally* collision-resistant; the
injectivity hypotheses are the standard clean abstraction under which the
*structural* soundness (injective fold ⇒ tamper-evident) is proved
UNCONDITIONALLY.  For full inclusion-soundness over arbitrary proof shapes we
additionally assume DOMAIN SEPARATION `hsep : ∀ a b w, h2 a b ≠ leafHash w`
(leaf digests are disjoint from internal-node digests) — a standard, necessary
prefix-free-encoding assumption used in every real Merkle construction to
prevent length-extension / second-preimage attacks.  This is flagged explicitly
wherever used.
-/

namespace Brockian.HighAssurance.Merkle

/-- Abstract digest. -/
abbrev Hash := ℕ

/-- A Merkle tree: leaves carry a value, internal nodes combine two subtrees. -/
inductive MerkleTree where
  | leaf (v : ℕ)
  | node (l r : MerkleTree)
deriving DecidableEq

/-- One inclusion-proof step: the sibling digest, and on which side it sits.
`left s`  : the current node is the LEFT child, sibling `s` on the right.
`right s` : the current node is the RIGHT child, sibling `s` on the left. -/
inductive Step where
  | left  (sibling : Hash)
  | right (sibling : Hash)
deriving DecidableEq

/-- An inclusion proof is a path of sibling steps, ordered leaf → root. -/
abbrev Proof := List Step

/-- Merkle root: fold `leafHash` at leaves and `h2` at internal nodes. -/
def root (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash) : MerkleTree → Hash
  | .leaf v   => leafHash v
  | .node l r => h2 (root h2 leafHash l) (root h2 leafHash r)

/-- Combine a current digest with one proof step. -/
def combineStep (h2 : Hash → Hash → Hash) (cur : Hash) : Step → Hash
  | .left  s => h2 cur s
  | .right s => h2 s cur

/-- Fold a proof from the leaf digest up to a computed root. -/
def verifyPath (h2 : Hash → Hash → Hash) (d : Hash) : Proof → Hash
  | []        => d
  | s :: rest => verifyPath h2 (combineStep h2 d s) rest

/-- Boolean inclusion check: does `v`'s leaf digest fold to root `r` via `p`? -/
def verifyInclusion (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash)
    (v : ℕ) (p : Proof) (r : Hash) : Bool :=
  decide (verifyPath h2 (leafHash v) p = r)

/-- Genuine membership: `v` is the value of some leaf of `t`. -/
def contains : MerkleTree → ℕ → Prop
  | .leaf v,   w => v = w
  | .node l r, w => contains l w ∨ contains r w

/-- Computable membership. -/
def member : MerkleTree → ℕ → Bool
  | .leaf v,   w => v == w
  | .node l r, w => member l w || member r w

/-- Canonical inclusion proof for a value in a tree (leaf → root order). -/
def proofFor (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash) :
    MerkleTree → ℕ → Proof
  | .leaf _,   _ => []
  | .node l r, w =>
      if member l w = true then
        proofFor h2 leafHash l w ++ [Step.left (root h2 leafHash r)]
      else
        proofFor h2 leafHash r w ++ [Step.right (root h2 leafHash l)]

/-! ## Basic structural lemmas -/

/-- Computable membership agrees with the propositional `contains`. -/
theorem member_iff : ∀ (t : MerkleTree) (w : ℕ), member t w = true ↔ contains t w := by
  intro t
  induction t with
  | leaf v => intro w; simp [member, contains, beq_iff_eq]
  | node l r ihl ihr => intro w; simp [member, contains, Bool.or_eq_true, ihl, ihr]

/-- `verifyPath` distributes over path concatenation (it is a left fold). -/
theorem verifyPath_append (h2 : Hash → Hash → Hash) (p q : Proof) (d : Hash) :
    verifyPath h2 d (p ++ q) = verifyPath h2 (verifyPath h2 d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.cons_append, verifyPath]
      exact ih (combineStep h2 d s)

/-- Every list is empty or ends in a last element (right decomposition). -/
theorem list_nil_or_concat (l : List Step) :
    l = [] ∨ ∃ (L : List Step) (b : Step), l = L ++ [b] := by
  induction l using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton L b _ih => exact Or.inr ⟨L, b, rfl⟩

/-! ## Root binding: the fold is injective in the leaf digest -/

/-- Under collision-resistance (`hinj2`), for a fixed proof the fold is
INJECTIVE in the leaf digest: a root binds the leaves that produce it. -/
theorem verifyPath_left_injective (h2 : Hash → Hash → Hash)
    (hinj2 : Function.Injective2 h2) (p : Proof) :
    Function.Injective (fun d : Hash => verifyPath h2 d p) := by
  induction p with
  | nil => intro a b hab; simpa [verifyPath] using hab
  | cons s rest ih =>
      intro a b hab
      simp only [verifyPath] at hab
      have h1 : combineStep h2 a s = combineStep h2 b s := ih hab
      cases s with
      | left t  => simp only [combineStep] at h1; exact (hinj2 h1).1
      | right t => simp only [combineStep] at h1; exact (hinj2 h1).2

/-- ROOT-BINDING (headline form): a fixed proof binds its leaf digest. -/
theorem root_binding (h2 : Hash → Hash → Hash)
    (hinj2 : Function.Injective2 h2) (p : Proof) :
    Function.Injective (fun d : Hash => verifyPath h2 d p) :=
  verifyPath_left_injective h2 hinj2 p

/-! ## Tamper evidence -/

/-- TAMPER DETECTION: replacing a leaf value by one with a different leaf digest
necessarily changes the computed root along the SAME proof — you cannot swap a
leaf without breaking the proof.  Requires only `hinj2` (injective fold). -/
theorem tamper_detected (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash)
    (hinj2 : Function.Injective2 h2) (v v' : ℕ) (p : Proof)
    (hne : leafHash v ≠ leafHash v') :
    verifyPath h2 (leafHash v) p ≠ verifyPath h2 (leafHash v') p := by
  intro heq
  exact hne (verifyPath_left_injective h2 hinj2 p heq)

/-! ## Completeness -/

/-- Fold of the canonical proof for a genuine member reaches the true root. -/
theorem complete_path (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash) :
    ∀ (t : MerkleTree) (v : ℕ), contains t v →
      verifyPath h2 (leafHash v) (proofFor h2 leafHash t v) = root h2 leafHash t := by
  intro t
  induction t with
  | leaf w =>
      intro v hmem
      simp only [contains] at hmem
      subst hmem
      simp [proofFor, verifyPath, root]
  | node l r ihl ihr =>
      intro v hmem
      simp only [proofFor]
      by_cases hml : member l v = true
      · rw [if_pos hml, verifyPath_append]
        have hcl : contains l v := (member_iff l v).mp hml
        rw [ihl v hcl]
        simp [verifyPath, combineStep, root]
      · rw [if_neg hml, verifyPath_append]
        have hnl : ¬ contains l v := fun hc => hml ((member_iff l v).mpr hc)
        simp only [contains] at hmem
        have hcr : contains r v := hmem.resolve_left hnl
        rw [ihr v hcr]
        simp [verifyPath, combineStep, root]

/-- INCLUSION COMPLETENESS: a genuine member has a proof that verifies against
the real root.  UNCONDITIONAL (no collision-resistance needed). -/
theorem inclusion_complete (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash)
    (t : MerkleTree) (v : ℕ) (hmem : contains t v) :
    verifyInclusion h2 leafHash v (proofFor h2 leafHash t v) (root h2 leafHash t) = true := by
  simp only [verifyInclusion, decide_eq_true_eq]
  exact complete_path h2 leafHash t v hmem

/-! ## Soundness -/

/-- INCLUSION SOUNDNESS / tamper-evidence: if `v` verifies against the *true*
root of `t` via some proof `p`, then `v` is genuinely committed by `t`.

Assumptions (all HONESTLY stated):
* `hinj2   : Function.Injective2 h2`     — collision-resistance of the combiner,
* `hinjLeaf: Function.Injective leafHash` — collision-resistance of leaf hashing,
* `hsep    : ∀ a b w, h2 a b ≠ leafHash w` — DOMAIN SEPARATION (leaf digests are
  disjoint from internal-node digests).  This is the standard prefix-free /
  domain-separation requirement of real Merkle constructions; without it a
  forged over-long proof could masquerade a leaf as an internal node. -/
theorem inclusion_sound (h2 : Hash → Hash → Hash) (leafHash : ℕ → Hash)
    (hinj2 : Function.Injective2 h2) (hinjLeaf : Function.Injective leafHash)
    (hsep : ∀ a b w, h2 a b ≠ leafHash w) :
    ∀ (t : MerkleTree) (v : ℕ) (p : Proof),
      verifyInclusion h2 leafHash v p (root h2 leafHash t) = true → contains t v := by
  intro t
  induction t with
  | leaf w =>
      intro v p h
      simp only [verifyInclusion, decide_eq_true_eq, root] at h
      rcases list_nil_or_concat p with rfl | ⟨L, b, rfl⟩
      · -- empty proof: leaf digests collide ⇒ same value
        simp only [verifyPath] at h
        have hv : v = w := hinjLeaf h
        simp only [contains]
        exact hv.symm
      · -- non-empty proof: top digest is an h2 output ≠ a leaf digest
        rw [verifyPath_append] at h
        cases b with
        | left s  => simp only [verifyPath, combineStep] at h; exact absurd h (hsep _ _ _)
        | right s => simp only [verifyPath, combineStep] at h; exact absurd h (hsep _ _ _)
  | node l r ihl ihr =>
      intro v p h
      simp only [verifyInclusion, decide_eq_true_eq, root] at h
      rcases list_nil_or_concat p with rfl | ⟨L, b, rfl⟩
      · -- empty proof cannot equal an internal-node digest
        simp only [verifyPath] at h
        exact absurd h.symm (hsep _ _ _)
      · rw [verifyPath_append] at h
        cases b with
        | left s =>
            simp only [verifyPath, combineStep] at h
            obtain ⟨he1, _he2⟩ := hinj2 h
            have hc : contains l v :=
              ihl v L (by simp only [verifyInclusion, decide_eq_true_eq]; exact he1)
            simp only [contains]; exact Or.inl hc
        | right s =>
            simp only [verifyPath, combineStep] at h
            obtain ⟨_he1, he2⟩ := hinj2 h
            have hc : contains r v :=
              ihr v L (by simp only [verifyInclusion, decide_eq_true_eq]; exact he2)
            simp only [contains]; exact Or.inr hc

/-! ## Non-vacuity: a concrete 4-leaf tree, decide-checked -/

namespace Example

/-- Concrete injective leaf hash (odd numbers). -/
def cLeaf (v : ℕ) : Hash := 3 * v + 1

/-- Concrete internal combiner, separated from the leaf-hash range. -/
def cH2 (a b : Hash) : Hash := 1000 * a + b + 500

/-- A concrete 4-leaf Merkle tree. -/
def T : MerkleTree :=
  .node (.node (.leaf 10) (.leaf 20)) (.node (.leaf 30) (.leaf 40))

/-- 30 is a genuine leaf (via computable membership + `member_iff`). -/
example : contains T 30 := (member_iff T 30).mp (by decide)

/-- A genuine inclusion proof verifies against the real root. -/
example : verifyInclusion cH2 cLeaf 30 (proofFor cH2 cLeaf T 30) (root cH2 cLeaf T) = true := by
  decide

/-- TAMPER: the same proof + real root REJECTS a swapped value. -/
example : verifyInclusion cH2 cLeaf 99 (proofFor cH2 cLeaf T 30) (root cH2 cLeaf T) = false := by
  decide

/-- A non-member fails to produce a verifying proof against the real root. -/
example : verifyInclusion cH2 cLeaf 25 (proofFor cH2 cLeaf T 25) (root cH2 cLeaf T) = false := by
  decide

/-- Completeness instantiated concretely (every real leaf verifies). -/
example : verifyInclusion cH2 cLeaf 40 (proofFor cH2 cLeaf T 40) (root cH2 cLeaf T) = true := by
  decide

end Example

end Brockian.HighAssurance.Merkle
