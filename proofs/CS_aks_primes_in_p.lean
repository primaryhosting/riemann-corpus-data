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

import Mathlib

/-!
# Introspective numbers

The key algebraic notion in the Agrawal–Kayal–Saxena primality test.
A natural number `m` is *introspective* for a polynomial `f` (with respect to the
modulus `X ^ r - 1`) if `f (X) ^ m ≡ f (X ^ m)` modulo `X ^ r - 1`.
-/

namespace AKS

open Polynomial

variable {R : Type*} [CommRing R]

/-- `m` is introspective for `f` modulo `X ^ r - 1`. -/
def Intro (r m : ℕ) (f : R[X]) : Prop :=
  (X ^ r - 1 : R[X]) ∣ f ^ m - f.comp (X ^ m)

lemma dvd_comp_of_cyclo_dvd {r m : ℕ} {g : R[X]} (h : (X ^ r - 1 : R[X]) ∣ g) :
    (X ^ r - 1 : R[X]) ∣ g.comp (X ^ m) := by
  obtain ⟨q, rfl⟩ := h
  rw [Polynomial.mul_comp]
  refine Dvd.dvd.mul_right ?_ _
  have h1 : ((X : R[X]) ^ r - 1).comp (X ^ m) = ((X : R[X]) ^ r) ^ m - 1 := by
    simp [← pow_mul, mul_comm]
  rw [h1]
  simpa using sub_dvd_pow_sub_pow ((X : R[X]) ^ r) 1 m

lemma Intro.one (r : ℕ) (f : R[X]) : Intro r 1 f := by
  simp [Intro]

lemma Intro.mul_exp {r m m' : ℕ} {f : R[X]} (h : Intro r m f) (h' : Intro r m' f) :
    Intro r (m * m') f := by
  unfold Intro at *
  have key := dvd_comp_of_cyclo_dvd (m := m) h'
  rw [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.comp_assoc] at key
  have e1 : f ^ (m * m') - f.comp (X ^ (m * m'))
      = ((f ^ m) ^ m' - (f.comp (X ^ m)) ^ m')
        + ((f.comp (X ^ m)) ^ m' - f.comp ((X ^ m').comp (X ^ m))) := by
    simp [← pow_mul]
    ring_nf
  rw [e1]
  exact dvd_add (dvd_trans h (sub_dvd_pow_sub_pow _ _ m')) key

lemma Intro.mul_poly {r m : ℕ} {f g : R[X]} (h : Intro r m f) (h' : Intro r m g) :
    Intro r m (f * g) := by
  unfold Intro at *
  have e : (f * g) ^ m - (f * g).comp (X ^ m)
      = (f ^ m - f.comp (X ^ m)) * g ^ m + f.comp (X ^ m) * (g ^ m - g.comp (X ^ m)) := by
    rw [Polynomial.mul_comp]; ring
  rw [e]
  exact dvd_add (h.mul_right _) (Dvd.dvd.mul_left h' _)

lemma Intro.prod {r m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (h : ∀ i ∈ s, Intro r m (f i)) : Intro r m (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa [Intro] using (Intro.one (R := R) r 1)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul_poly
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Evaluation form of introspectivity at an `r`-th root of unity. -/
lemma Intro.eval_pow {K : Type*} [CommRing K] {r m : ℕ} {f : K[X]} (h : Intro r m f)
    {z : K} (hz : z ^ r = 1) : f.eval (z ^ m) = (f.eval z) ^ m := by
  unfold Intro at h
  obtain ⟨q, hq⟩ := h
  have h2 := congrArg (Polynomial.eval z) hq
  simp [hz, Polynomial.eval_comp] at h2
  linarith [h2, sub_eq_zero.mp h2]

/-- In characteristic `p`, every polynomial over `ZMod p` is introspective for `p`. -/
lemma intro_char_prime {p : ℕ} [Fact (Nat.Prime p)] (r : ℕ) (f : (ZMod p)[X]) :
    Intro r p f := by
  have hcomp : f.comp (X ^ p) = f ^ p := by
    rw [← Polynomial.expand_eq_comp_X_pow]
    have h := Polynomial.map_frobenius_expand (R := ZMod p) (p := p) (f := f)
    rw [ZMod.frobenius_zmod] at h
    simpa using h
  simp [Intro, hcomp]

end AKS

