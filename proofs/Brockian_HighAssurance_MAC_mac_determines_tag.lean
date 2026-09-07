import Mathlib

/-!
# Message-Authentication-Code (MAC) security: the correctness + unforgeability core

A **MAC** protects the *integrity and authenticity* of a message under a shared
secret key: the holder of key `k` computes a short **tag** `mac k m` for a
message `m`; anyone else holding `k` can `verify` that a received `(m, t)` pair
was tagged by a key-holder, and an adversary *without* the key should be unable
to produce a fresh valid `(m, t)`.

This file formalises the **abstract, keyed-tag-function model** of a MAC — the
same shape Galois verifies with Cryptol/SAW: an uninterpreted `mac : Key → Msg →
Tag` stands for any concrete keyed construction (HMAC, CMAC, GMAC, …), and the
security-relevant *structure* is proved once, independently of the arithmetic.

We separate, honestly, two kinds of guarantee:

* **Structural guarantees — proved UNCONDITIONALLY** (no cryptographic
  assumption): correctness (`verify_correct`), soundness/consistency
  (`verify_sound`, `verify_reject`), the *uniqueness anchor*
  (`mac_determines_tag` — every message has exactly one valid tag under a key,
  so blind guessing is the only structure-respecting attack), the fact that a
  forgery *pins down* the true tag (`forgery_reveals_tag`), and cross-key
  rejection / key-separation (`cross_key_rejects`).

* **Computational unforgeability — proved UNDER A NAMED HARDNESS ASSUMPTION.**
  Whether an adversary can actually *produce* `mac k m` for a fresh `m` is a
  computational hypothesis (`hHard`), not a theorem of arithmetic; we model it
  explicitly and derive `no_forgery` from it. We are candid that this leg is
  conditional — that is exactly what MAC security *is*.
-/

namespace Brockian.HighAssurance.MAC

/-! ## The abstract MAC over a keyed tag function -/

section Abstract

variable {Key Msg Tag : Type} [DecidableEq Tag]

/-- **Verification.** Recompute the tag under the key and compare: a received
    pair `(m, t)` is accepted iff `t` is the honest tag `mac k m`. This is the
    universal shape of a deterministic MAC verifier. -/
def verify (mac : Key → Msg → Tag) (k : Key) (m : Msg) (t : Tag) : Bool :=
  decide (mac k m = t)

/-- **Correctness.** An honestly produced tag always verifies: the legitimate
    key-holder is never rejected. -/
theorem verify_correct (mac : Key → Msg → Tag) (k : Key) (m : Msg) :
    verify mac k m (mac k m) = true := by
  simp [verify]

/-- **Soundness / consistency.** `verify` accepts ONLY the correct tag: if a pair
    is accepted, the tag it carries is exactly the honest tag. (No false accepts.) -/
theorem verify_sound (mac : Key → Msg → Tag) (k : Key) (m : Msg) (t : Tag)
    (h : verify mac k m t = true) : t = mac k m := by
  unfold verify at h
  exact (of_decide_eq_true h).symm

/-- **Rejection.** Any tag other than the honest one is rejected — the
    contrapositive completeness statement. -/
theorem verify_reject (mac : Key → Msg → Tag) (k : Key) (m : Msg) (t : Tag)
    (h : t ≠ mac k m) : verify mac k m t = false := by
  unfold verify
  exact decide_eq_false (fun heq => h heq.symm)

/-- **Uniqueness anchor (the real structural content).** Under a fixed key, a
    message has a UNIQUE valid tag: any two accepted tags for the same message
    are equal. Hence the *only* way to make `verify` accept is to hit the single
    correct value — blind guessing, whose success probability is `1/|Tag|`. This
    is the honest, fully unconditional heart of MAC security. -/
theorem mac_determines_tag (mac : Key → Msg → Tag) (k : Key) (m : Msg)
    (t₁ t₂ : Tag) (h₁ : verify mac k m t₁ = true) (h₂ : verify mac k m t₂ = true) :
    t₁ = t₂ :=
  (verify_sound mac k m t₁ h₁).trans (verify_sound mac k m t₂ h₂).symm

/-- **A forgery reveals the tag.** Any pair that verifies necessarily carries the
    true tag `mac k m`; so "forging a valid tag for `m`" is *equivalent to*
    "computing `mac k m`". This reduction is what makes the hardness assumption
    below the right one. -/
theorem forgery_reveals_tag (mac : Key → Msg → Tag) (k : Key) (m : Msg) (t : Tag)
    (h : verify mac k m t = true) : t = mac k m :=
  verify_sound mac k m t h

/-! ## The unforgeability game -/

/-- **A forgery.** The adversary outputs `(m, t)` such that: `t` verifies for `m`
    under `k`; the exact pair `(m, t)` was never seen; and — crucially — the
    message `m` was NEVER authenticated at all (no tag for `m` appears in
    `seen`). This is *existential* forgery on a fresh message. -/
def Forged (mac : Key → Msg → Tag) (k : Key) (seen : Finset (Msg × Tag))
    (m : Msg) (t : Tag) : Prop :=
  verify mac k m t = true ∧ (m, t) ∉ seen ∧ (∀ t', (m, t') ∉ seen)

/-- Even a forgery on a fresh message pins the true tag: a successful existential
    forgery is exactly a computation of `mac k m`. -/
theorem forged_reveals_tag (mac : Key → Msg → Tag) (k : Key)
    (seen : Finset (Msg × Tag)) (m : Msg) (t : Tag) (h : Forged mac k seen m t) :
    t = mac k m :=
  forgery_reveals_tag mac k m t h.1

/-- **Existential unforgeability under the MAC hardness assumption.**

    We make the cryptographic content explicit and honest via two named premises:

    * `hReveal` — the *reduction* (proved unconditionally as `forged_reveals_tag`,
      supplied here as the modelling link): producing a valid tag for a message
      that was never authenticated constitutes *computing* `mac k` on that fresh
      message, i.e. it witnesses `CanCompute k m`;
    * `hHard` — the **hardness assumption**: the adversary CANNOT compute `mac k`
      on any message it never had authenticated.

    From these, **no forgery exists**. The structural half (`hReveal`) is a
    theorem; the security half (`hHard`) is a stated assumption — this is a
    faithful statement of what a MAC guarantees. -/
theorem no_forgery (mac : Key → Msg → Tag) (k : Key) (seen : Finset (Msg × Tag))
    (CanCompute : Key → Msg → Prop)
    (hReveal : ∀ m t, Forged mac k seen m t → CanCompute k m)
    (hHard : ∀ m, (∀ t, (m, t) ∉ seen) → ¬ CanCompute k m) :
    ¬ ∃ m t, Forged mac k seen m t := by
  rintro ⟨m, t, hf⟩
  exact hHard m hf.2.2 (hReveal m t hf)

/-- **Key separation.** If two keys assign different tags to a message (a
    property any good keyed function has for `k₁ ≠ k₂`), then a tag valid under
    `k₁` is REJECTED under `k₂`: cross-key forgery — replaying a tag against a
    different key — fails. -/
theorem cross_key_rejects (mac : Key → Msg → Tag) (k₁ k₂ : Key) (m : Msg)
    (hsep : mac k₁ m ≠ mac k₂ m) : verify mac k₂ m (mac k₁ m) = false := by
  unfold verify
  exact decide_eq_false (fun heq => hsep heq.symm)

end Abstract

/-! ## Non-vacuity: a concrete keyed tag function over `ℕ`

`cmac k m = k · 2654435761 + m` — a Knuth-multiplicative key mix, standing in
for a real construction, enough to exhibit every property on closed values by
kernel computation (`decide`). -/

/-- A concrete keyed tag function. -/
def cmac (k m : ℕ) : ℕ := k * 2654435761 + m

/-- Correctness on concrete values: the honest tag verifies. -/
example : verify cmac 3 7 (cmac 3 7) = true := by decide

/-- …and via the general theorem, not just by luck. -/
example : verify cmac 3 7 (cmac 3 7) = true := verify_correct cmac 3 7

/-- A WRONG tag is rejected (no false accept). -/
example : verify cmac 3 7 999 = false := by decide

/-- Soundness bites concretely: the only accepted tag for `(3,7)` equals `cmac 3 7`. -/
example : verify cmac 3 7 42 = true → (42 : ℕ) = cmac 3 7 := verify_sound cmac 3 7 42

/-- Two distinct keys really do separate tags on a message… -/
example : cmac 1 5 ≠ cmac 2 5 := by decide

/-- …so a tag forged under key `1` is rejected under key `2` (concrete
    `cross_key_rejects`). -/
example : verify cmac 2 0 (cmac 1 0) = false := by decide

/-- …the same instance, obtained from the general key-separation theorem. -/
example : verify cmac 2 0 (cmac 1 0) = false :=
  cross_key_rejects cmac 1 2 0 (by decide)

/-- The `Forged` predicate is NON-VACUOUS: an adversary who *does* know the key
    (empty `seen`) satisfies it — which is precisely why `no_forgery` must rest on
    the hardness assumption `hHard`, and cannot be a theorem of arithmetic alone. -/
example : Forged cmac 3 (∅ : Finset (ℕ × ℕ)) 7 (cmac 3 7) := by
  refine ⟨by decide, ?_, ?_⟩
  · simp
  · intro t'; simp

/-- Uniqueness anchor, concretely: any accepted tag for `(3,7)` is forced. -/
example (t : ℕ) (h : verify cmac 3 7 t = true) : t = cmac 3 7 :=
  mac_determines_tag cmac 3 7 t (cmac 3 7) h (verify_correct cmac 3 7)

end Brockian.HighAssurance.MAC
