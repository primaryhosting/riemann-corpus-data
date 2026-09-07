import Mathlib

/-!
# Authenticated Encryption with Associated Data (AEAD): correctness + ciphertext integrity

A machine-checked, non-vacuous formalization of the classical **Encrypt-then-MAC**
AEAD composition (Bellare–Namprempre 2000; Krawczyk 2001).  The construction couples

* an underlying (invertible) cipher `enc`/`dec` with correctness
  `dec k n (enc k n p) = p`, and
* a message-authentication code `mac`,

into a sealed ciphertext `(c, t) := (enc k n p, mac k (n, c))` and a *fail-closed*
opener that rejects unless the stored tag matches the recomputed MAC.

We prove, **unconditionally on the model**:

* **Correctness / roundtrip** — sealing then opening recovers the plaintext.
* **Authenticity required** — anything the opener accepts carries the authentic tag
  `t = mac k (n, c)`; nothing else is ever decrypted (fail-closed).
* **Tamper rejection** — modifying the ciphertext under a fixed authentic tag is
  rejected whenever the MAC separates the two ciphertexts (collision-freedom
  hypothesis — the honest computational-unforgeability abstraction of a real MAC).
* **Nonce binding** — a valid seal replayed under a different nonce is rejected
  when the MAC separates the nonces.

Honest boundary: MAC unforgeability is a *computational* assumption, here modeled
as collision-freedom / injectivity of `mac` in its ciphertext (resp. nonce)
argument.  The AEAD **composition** guarantees are proved with no such assumption.
A concrete XOR-stream cipher + XOR-mixing MAC over `ℕ` witnesses every hypothesis
(the MAC is provably injective in its ciphertext argument) and discharges the
roundtrip/tamper/wrong-tag behaviours by `decide`.
-/

namespace Brockian.HighAssurance.AEAD

variable {Key Nonce Plain Cipher Tag : Type}

/-- Seal a plaintext: encrypt, then MAC the (nonce, ciphertext) pair
    (Encrypt-then-MAC).  The AEAD ciphertext is the pair `(c, t)`. -/
def aeadSeal (enc : Key → Nonce → Plain → Cipher) (mac : Key → Nonce × Cipher → Tag)
    (k : Key) (n : Nonce) (p : Plain) : Cipher × Tag :=
  (enc k n p, mac k (n, enc k n p))

/-- Open an AEAD ciphertext.  **Fail-closed**: decrypt *only* if the recomputed
    MAC over `(nonce, ciphertext)` equals the stored tag; otherwise reject. -/
def open_ [DecidableEq Tag]
    (dec : Key → Nonce → Cipher → Plain) (mac : Key → Nonce × Cipher → Tag)
    (k : Key) (n : Nonce) (ct : Cipher × Tag) : Option Plain :=
  if mac k (n, ct.1) = ct.2 then some (dec k n ct.1) else none

/-- **Correctness (roundtrip).**  Given correctness of the underlying cipher
    (`dec k n (enc k n p) = p`), sealing then opening recovers the plaintext.
    Unconditional on the model apart from the stated cipher-correctness hypothesis. -/
theorem aead_roundtrip [DecidableEq Tag]
    (enc : Key → Nonce → Plain → Cipher) (dec : Key → Nonce → Cipher → Plain)
    (mac : Key → Nonce × Cipher → Tag) (k : Key) (n : Nonce) (p : Plain)
    (hdec : dec k n (enc k n p) = p) :
    open_ dec mac k n (aeadSeal enc mac k n p) = some p := by
  simp [open_, aeadSeal, hdec]

/-- **Authenticity required (fail-closed).**  Whatever the opener accepts must
    carry the authentic tag: if `open_` returns `some _` on `(c, t)`, then
    `t = mac k (n, c)`.  Proved unconditionally on the model. -/
theorem auth_required [DecidableEq Tag]
    (dec : Key → Nonce → Cipher → Plain) (mac : Key → Nonce × Cipher → Tag)
    (k : Key) (n : Nonce) (c : Cipher) (t : Tag) (p : Plain)
    (h : open_ dec mac k n (c, t) = some p) :
    t = mac k (n, c) := by
  by_cases hcond : mac k (n, c) = t
  · exact hcond.symm
  · simp [open_, hcond] at h

/-- **Tamper rejection.**  Replacing the ciphertext `c` by any `c'` the MAC
    separates (`mac k (n,c) ≠ mac k (n,c')`), under the authentic tag
    `t = mac k (n,c)`, is rejected: `open_` returns `none`.  The MAC-separation
    premise is the honest collision-freedom abstraction of MAC unforgeability;
    the rejection itself is proved unconditionally on the model. -/
theorem tamper_rejected [DecidableEq Tag]
    (dec : Key → Nonce → Cipher → Plain) (mac : Key → Nonce × Cipher → Tag)
    (k : Key) (n : Nonce) (c c' : Cipher) (t : Tag)
    (hne : mac k (n, c) ≠ mac k (n, c')) (hauth : t = mac k (n, c)) :
    open_ dec mac k n (c', t) = none := by
  have hcond : mac k (n, c') ≠ t := by rw [hauth]; exact fun h => hne h.symm
  simp [open_, hcond]

/-- **Nonce binding (replay rejection).**  A seal produced under nonce `n`,
    replayed under a different nonce `n'` the MAC separates, is rejected.
    Rejection is unconditional on the model given the MAC-separation premise. -/
theorem replay_rejected [DecidableEq Tag]
    (enc : Key → Nonce → Plain → Cipher) (dec : Key → Nonce → Cipher → Plain)
    (mac : Key → Nonce × Cipher → Tag) (k : Key) (n n' : Nonce) (p : Plain)
    (hne : mac k (n', enc k n p) ≠ mac k (n, enc k n p)) :
    open_ dec mac k n' (aeadSeal enc mac k n p) = none := by
  simp [open_, aeadSeal, hne]

/-!
## A concrete, computable witness (XOR-stream cipher + XOR-mixing MAC over `ℕ`)

Everything above is discharged by an explicit construction, proving non-vacuity:
the model is inhabited, the cipher-correctness hypothesis holds unconditionally,
and the MAC is *provably* injective in its ciphertext argument — so the
collision-freedom premise of `tamper_rejected` is genuinely satisfiable.
-/

/-- A key/nonce-derived keystream word. -/
def ks (k n : ℕ) : ℕ := (2 * k + 1) ^^^ (3 * n + 7)

/-- XOR-stream encryption (self-inverse). -/
def cEnc (k n p : ℕ) : ℕ := p ^^^ ks k n

/-- XOR-stream decryption (same operation as `cEnc`). -/
def cDec (k n c : ℕ) : ℕ := c ^^^ ks k n

/-- A concrete MAC that mixes key and nonce, then XORs the ciphertext word. -/
def cMac (k : ℕ) (nc : ℕ × ℕ) : ℕ := (5 * k + 7 * nc.1 + 3) ^^^ nc.2

/-- **Cipher correctness for the concrete construction (unconditional).** -/
theorem cDec_cEnc (k n p : ℕ) : cDec k n (cEnc k n p) = p := by
  simp only [cDec, cEnc, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Left-cancellation of XOR on `ℕ`. -/
theorem xor_left_cancel {a b c : ℕ} (h : a ^^^ b = a ^^^ c) : b = c := by
  have h2 : a ^^^ (a ^^^ b) = a ^^^ (a ^^^ c) := by rw [h]
  simpa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using h2

/-- **The concrete MAC is injective in its ciphertext argument** — it provably
    satisfies the collision-freedom premise used by `tamper_rejected`. -/
theorem cMac_inj2 (k n : ℕ) {c c' : ℕ} (h : c ≠ c') :
    cMac k (n, c) ≠ cMac k (n, c') := by
  simpa [cMac] using h

/-- **Unconditional concrete roundtrip** (no cipher-correctness hypothesis needed
    — it is discharged by `cDec_cEnc`). -/
theorem concrete_roundtrip (k n p : ℕ) :
    open_ cDec cMac k n (aeadSeal cEnc cMac k n p) = some p :=
  aead_roundtrip cEnc cDec cMac k n p (cDec_cEnc k n p)

/-- **Unconditional concrete tamper rejection**: for the concrete construction,
    *any* modification of the ciphertext (`c ≠ c'`) under the authentic tag is
    rejected — the MAC-separation premise is discharged by `cMac_inj2`. -/
theorem concrete_tamper_rejected (k n c c' t : ℕ) (hne : c ≠ c')
    (hauth : t = cMac k (n, c)) :
    open_ cDec cMac k n (c', t) = none :=
  tamper_rejected cDec cMac k n c c' t (cMac_inj2 k n hne) hauth

/-!
### `decide`-checked non-vacuity witnesses (fully concrete numerics)
-/

/-- (a) A sealed message opens to the original plaintext. -/
example : open_ cDec cMac 42 7 (aeadSeal cEnc cMac 42 7 99) = some 99 := by decide

/-- (b) A ciphertext tampered (one bit flipped) under the authentic tag is
    rejected — decryption fails closed. -/
example :
    open_ cDec cMac 42 7 (cEnc 42 7 99 ^^^ 1, cMac 42 (7, cEnc 42 7 99)) = none := by
  decide

/-- (c) A wrong tag is rejected. -/
example :
    open_ cDec cMac 42 7 (cEnc 42 7 99, cMac 42 (7, cEnc 42 7 99) ^^^ 1) = none := by
  decide

end Brockian.HighAssurance.AEAD
