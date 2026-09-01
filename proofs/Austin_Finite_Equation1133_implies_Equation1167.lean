import Mathlib
import RequestProject.Austin.Defs
import RequestProject.Austin.FiniteLemmas
import RequestProject.Austin.AustinLaws
import RequestProject.Austin.Implications
import RequestProject.Austin.Eq1133
import RequestProject.Austin.InfiniteModel3994
import RequestProject.Austin.InfiniteModel374794
import RequestProject.Austin.InfiniteModel28770
import RequestProject.Austin.TwoVariableLaws

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

import RequestProject.Austin.Defs

/-!
# Finite implications 1133 → 1167 → 1096

Propositions 5.11 and 5.12: for finite magmas, equation 1133 implies equation 1167,
which in turn implies equation 1096.
-/

namespace Austin

variable {G : Type*} [Mul G] [Finite G]

/-! ### 1133 implies 1167 -/

section Eq1133

variable (h : Equation1133 G)
include h

omit [Finite G] in
/-- Taking `z = y ◇ (y ◇ y)` in 1133 gives `y ◇ (z ◇ y) = y`. -/
private theorem Eq1133.aux_fix (y : G) : y * ((y * (y * y)) * y) = y := (h y y y).symm

omit [Finite G] in
/-- Left multiplication is an involution. -/
private theorem Eq1133.involutive (y x : G) : y * (y * x) = x := by
  have hx := h x y (y * (y * y))
  rw [Eq1133.aux_fix h y] at hx
  exact hx.symm

omit [Finite G] in
private theorem Eq1133.left_inj (y : G) : Function.Injective (fun a : G => y * a) := by
  intro a b hab
  simp only at hab
  rw [← Eq1133.involutive h y a, ← Eq1133.involutive h y b, hab]

omit [Finite G] in
/-- The key identity `L_{(z ◇ y) ◇ y} = L_{z ◇ y}`. -/
private theorem Eq1133.star (y z x : G) : ((z * y) * y) * x = (z * y) * x := by
  have h1 : x = (z * y) * (((z * y) * (z * (z * y))) * x) := h x (z * y) z
  rw [Eq1133.involutive h z y] at h1
  refine Eq1133.left_inj h (z * y) ?_
  show (z * y) * (((z * y) * y) * x) = (z * y) * ((z * y) * x)
  rw [Eq1133.involutive h (z * y) x, ← h1]

omit [Finite G] in
/-- Squaring is surjective: `((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y) = y`. -/
private theorem Eq1133.sq_surj (y : G) : ((y * y) * y) * ((y * y) * y) = y := by
  have h1 : ((y * y) * y) * y = (y * y) * y := Eq1133.star h y y y
  have h2 : ((y * y) * y) * (((y * y) * y) * y) = y := Eq1133.involutive h ((y * y) * y) y
  rw [h1] at h2
  exact h2

/-- **On a finite magma, equation 1133 implies equation 1167.** -/
theorem Finite.Equation1133_implies_Equation1167 : Equation1167 G := by
  have hSinj : Function.Injective (fun t : G => t * t) :=
    (Finite.injective_iff_surjective (α := G)).2
      (fun y => ⟨(y * y) * y, Eq1133.sq_surj h y⟩)
  intro x y z
  set w : G := (z * (y * y)) * (y * y) with hw
  have hstar : ∀ a : G, w * a = (z * (y * y)) * a := Eq1133.star h (y * y) z
  -- `w ◇ w = y ◇ y`
  have e1 : w * (w * w) = w := Eq1133.involutive h w w
  have e2 : w * (y * y) = w := by rw [hstar (y * y)]
  have e3 : w * w = y * y := by
    refine Eq1133.left_inj h w ?_
    show w * (w * w) = w * (y * y)
    rw [e1, e2]
  have hwy : w = y := hSinj e3
  calc x = y * (y * x) := (Eq1133.involutive h y x).symm
    _ = y * (w * x) := by rw [hwy]
    _ = y * ((z * (y * y)) * x) := by rw [hstar x]

end Eq1133

/-! ### 1167 implies 1096 -/

section Eq1167

variable (h : Equation1167 G)
include h

private theorem Eq1167.left_inj (y : G) : Function.Injective (fun a : G => y * a) :=
  (Finite.injective_iff_surjective (α := G)).2
    (fun x => ⟨(x * (y * y)) * x, (h x y x).symm⟩)

/-- The inverse relation in the other order: `(z ◇ (y ◇ y)) ◇ (y ◇ a) = a`. -/
private theorem Eq1167.right_inverse (y z a : G) : (z * (y * y)) * (y * a) = a := by
  refine Eq1167.left_inj h y ?_
  show y * ((z * (y * y)) * (y * a)) = y * a
  exact (h (y * a) y z).symm

/-- Squaring is surjective, hence bijective. -/
private theorem Eq1167.sq_inj : Function.Injective (fun t : G => t * t) := by
  intro a b hab
  simp only at hab
  have e1 : ((a * a) * (a * a)) * (a * a) = a := Eq1167.right_inverse h a (a * a) a
  have e2 : ((b * b) * (b * b)) * (b * b) = b := Eq1167.right_inverse h b (b * b) b
  rw [hab] at e1
  exact e1.symm.trans e2

private theorem Eq1167.sq_surj : Function.Surjective (fun t : G => t * t) :=
  Finite.surjective_of_injective (Eq1167.sq_inj h)

/-- `L_{z ◇ y}` does not depend on `z`. -/
private theorem Eq1167.left_indep (y z z' a : G) : (z * y) * a = (z' * y) * a := by
  obtain ⟨u, hu⟩ := Eq1167.sq_surj h y
  simp only at hu
  refine Eq1167.left_inj h u ?_
  show u * ((z * y) * a) = u * ((z' * y) * a)
  rw [← hu]
  exact ((h a u z).symm).trans (h a u z')

/-- The main computation: `(x ◇ (z ◇ y)) ◇ x = y ◇ x`. -/
private theorem Eq1167.key (y z x : G) : (x * (z * y)) * x = y * x := by
  obtain ⟨b, hb⟩ := Eq1167.sq_surj h z
  obtain ⟨a, ha⟩ := Eq1167.sq_surj h b
  simp only at hb ha
  have hy : a * (z * y) = y := by
    have := h y a b
    rw [ha, hb] at this
    exact this.symm
  rw [Eq1167.left_indep h (z * y) x a x, hy]

/-- **On a finite magma, equation 1167 implies equation 1096.** -/
theorem Finite.Equation1167_implies_Equation1096 : Equation1096 G := by
  intro x y z
  calc x = y * ((x * (y * y)) * x) := h x y x
    _ = y * (y * x) := by rw [Eq1167.key h y y x]
    _ = y * ((x * (z * y)) * x) := by rw [Eq1167.key h y z x]

end Eq1167

end Austin

import Mathlib

/-!
# General lemmas about self-maps of a finite set

These are the three general lemmas used to derive implications that hold for finite
magmas: two variants of "one-sided inverses on a finite set are two-sided", and the
eventual periodicity of iteration.
-/

namespace Austin

variable {X : Type*} [Finite X]

/-- **Eventual period.** For a self-map of a finite set there is `n ≥ 1` with
`f^[2n] = f^[n]`. -/
theorem exists_iterate_two_mul_eq (f : X → X) : ∃ n, 1 ≤ n ∧ f^[2 * n] = f^[n] := by
  have : ¬ Function.Injective (fun n : ℕ => f^[n]) := by
    intro hinj
    exact (Set.infinite_range_of_injective hinj).not_finite (Set.toFinite _)
  rw [Function.not_injective_iff] at this
  obtain ⟨a, b, hab, hne⟩ := this
  -- normalise so that `m < m + n`
  obtain ⟨m, n, hn1, hmn⟩ :
      ∃ m n : ℕ, 1 ≤ n ∧ f^[m + n] = f^[m] := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b - a, by omega, by rw [show a + (b - a) = b by omega]; exact hab.symm⟩
    · exact ⟨b, a - b, by omega, by rw [show b + (a - b) = a by omega]; exact hab⟩
  have hstep : ∀ t : ℕ, f^[m + t + n] = f^[m + t] := by
    intro t
    funext x
    have h1 : m + t + n = t + (m + n) := by omega
    rw [h1, Function.iterate_add_apply, hmn, ← Function.iterate_add_apply,
      show t + m = m + t by omega]
  have key : ∀ j t : ℕ, f^[m + t + j * n] = f^[m + t] := by
    intro j
    induction j with
    | zero => intro t; simp
    | succ j ih =>
        intro t
        have h1 : m + t + (j + 1) * n = m + (t + j * n) + n := by ring
        rw [h1, hstep (t + j * n)]
        have h2 : m + (t + j * n) = m + t + j * n := by omega
        rw [h2, ih t]
  refine ⟨n * (m + 1), Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  have hN : m ≤ n * (m + 1) := by nlinarith
  have h1 : 2 * (n * (m + 1)) = m + (n * (m + 1) - m) + (m + 1) * n := by
    have : n * (m + 1) = (m + 1) * n := by ring
    omega
  have h2 : n * (m + 1) = m + (n * (m + 1) - m) := by omega
  rw [h1, key, ← h2]

/-- If the image of `f` is contained in the image of `f ∘ f`, then `f^[m+1] = f` for
some `m ≥ 1`; in particular `f` is a bijection on its image. -/
theorem exists_iterate_succ_eq_of_mem_range (f : X → X) (h : ∀ x, ∃ y, f x = f (f y)) :
    ∃ m, 1 ≤ m ∧ f^[m + 1] = f := by
  have key : ∀ k : ℕ, ∀ x, ∃ y, f x = f^[k + 1] y := by
    intro k
    induction k with
    | zero => intro x; exact ⟨x, rfl⟩
    | succ k ih =>
        intro x
        obtain ⟨u, hu⟩ := h x
        obtain ⟨w, hw⟩ := ih u
        exact ⟨w, by rw [hu, hw, ← Function.iterate_succ_apply' f (k + 1) w]⟩
  obtain ⟨n, hn1, hn⟩ := exists_iterate_two_mul_eq f
  refine ⟨n, hn1, funext fun x => ?_⟩
  obtain ⟨y, hy⟩ := key (n - 1) x
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at hy
  calc f^[n + 1] x = f^[n] (f x) := by rw [Function.iterate_succ_apply]
    _ = f^[n] (f^[n] y) := by rw [hy]
    _ = f^[2 * n] y := by rw [← Function.iterate_add_apply]; ring_nf
    _ = f^[n] y := by rw [hn]
    _ = f x := hy.symm

/-- If `f x` is determined by `f (f x)`, then `f^[m+1] = f` for some `m ≥ 1`. -/
theorem exists_iterate_succ_eq_of_inj (f : X → X)
    (h : ∀ a b, f (f a) = f (f b) → f a = f b) : ∃ m, 1 ≤ m ∧ f^[m + 1] = f := by
  have key : ∀ k : ℕ, ∀ a b, f^[k + 1] a = f^[k + 1] b → f a = f b := by
    intro k
    induction k with
    | zero => intro a b hab; simpa using hab
    | succ k ih =>
        intro a b hab
        have h1 : f^[k + 1] (f a) = f^[k + 1] (f b) := by
          rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply]
          exact hab
        exact h _ _ (ih _ _ h1)
  obtain ⟨n, hn1, hn⟩ := exists_iterate_two_mul_eq f
  refine ⟨n, hn1, funext fun x => ?_⟩
  have hn' : n - 1 + 1 = n := by omega
  have h2 : f^[n] (f^[n] x) = f^[n] x := by
    rw [← Function.iterate_add_apply, show n + n = 2 * n by ring, hn]
  have := key (n - 1) (f^[n] x) x (by rw [hn']; exact h2)
  rw [Function.iterate_succ_apply']
  exact this

/-- **Lemma (`ffg`).** Let `X` be finite and `f g : X → X` with `f = f ∘ f ∘ g`.
Then `f = f ∘ g ∘ f`. -/
theorem f_ffg_implies_f_fgf (f g : X → X) (hfg : f = f ∘ f ∘ g) : f = f ∘ g ∘ f := by
  have h : ∀ x, f x = f (f (g x)) := fun x => congrFun hfg x
  obtain ⟨m, hm1, hm⟩ := exists_iterate_succ_eq_of_mem_range f (fun x => ⟨g x, h x⟩)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  funext x
  have hsplit : ∀ w, f^[m' + 1 + 1] w = f^[m'] (f (f w)) := by
    intro w
    rw [show m' + 1 + 1 = m' + 2 by ring, Function.iterate_add_apply]
    simp [Function.iterate_succ_apply]
  show f x = f (g (f x))
  calc f x = f^[m' + 1 + 1] x := by rw [hm]
    _ = f^[m'] (f (f x)) := hsplit x
    _ = f^[m'] (f (f (g (f x)))) := by rw [← h (f x)]
    _ = f^[m' + 1 + 1] (g (f x)) := (hsplit _).symm
    _ = f (g (f x)) := by rw [hm]

/-- **Lemma (`gff`).** Let `X` be finite and `f g : X → X` with `f = g ∘ f ∘ f`.
Then `f = f ∘ g ∘ f`. -/
theorem f_gff_implies_f_fgf (f g : X → X) (hfg : f = g ∘ f ∘ f) : f = f ∘ g ∘ f := by
  have h : ∀ x, f x = g (f (f x)) := fun x => congrFun hfg x
  obtain ⟨m, hm1, hm⟩ := exists_iterate_succ_eq_of_inj f (by
    intro a b hab
    rw [h a, h b, hab])
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  funext x
  have hsplit : ∀ w, f^[m' + 1 + 1] w = f (f (f^[m'] w)) := by
    intro w
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  show f x = f (g (f x))
  calc f x = f^[m' + 1 + 1] x := by rw [hm]
    _ = f (f (f^[m'] x)) := hsplit x
    _ = f (g (f (f (f^[m'] x)))) := by rw [← h (f^[m'] x)]
    _ = f (g (f^[m' + 1 + 1] x)) := by rw [hsplit]
    _ = f (g (f x)) := by rw [hm]

end Austin

import RequestProject.Austin.Defs

/-!
# Austin's finite model theorem for laws in two variables

Theorem 5.4.  A law in (at most) two variables which has a variable occurring on *both*
sides admits a non-trivial finite model.  (The extra hypothesis is necessary: the law
`x = y ◇ y` has no non-trivial model at all.)

The models are the "affine" magmas `u ◇ v = (1 - c) * u + c * v` on `ZMod k`.  A word `w`
in the two variables evaluates in such a magma to `P w (c) * x + (1 - P w (c)) * y`, where
`P w ∈ ℤ[c]` is defined by `P X = 1`, `P Y = 0`,
`P (a ◇ b) = (1 - c) * P a + c * P b`.  So the law `s = t` holds as soon as
`(P s - P t)(c) = 0` in `ZMod k`.  Evaluating at `c = 1/2` shows that the integer
polynomial `D = P s - P t` is not the constant `1` or `-1`, hence some integer value
`D(c₀)` has absolute value `≠ 1`, and we may take `k = |D(c₀)|` (or `k = 2` when the value
is `0`).
-/

namespace Austin

/-- Words in two variables `X` and `Y`. -/
inductive TwoVarWord where
  | X : TwoVarWord
  | Y : TwoVarWord
  | op : TwoVarWord → TwoVarWord → TwoVarWord
deriving DecidableEq

namespace TwoVarWord

/-- Evaluation of a word for a given binary operation. -/
def evalF {G : Type*} (f : G → G → G) (x y : G) : TwoVarWord → G
  | X => x
  | Y => y
  | op a b => f (evalF f x y a) (evalF f x y b)

/-- Evaluation of a word in a magma. -/
def evalM {G : Type*} [Mul G] (x y : G) (w : TwoVarWord) : G := evalF (· * ·) x y w

/-- The variable `X` occurs in the word. -/
def occX : TwoVarWord → Prop
  | X => True
  | Y => False
  | op a b => occX a ∨ occX b

/-- The variable `Y` occurs in the word. -/
def occY : TwoVarWord → Prop
  | X => False
  | Y => True
  | op a b => occY a ∨ occY b

/-- Swap the two variables. -/
def swapVars : TwoVarWord → TwoVarWord
  | X => Y
  | Y => X
  | op a b => op (swapVars a) (swapVars b)

theorem evalF_swapVars {G : Type*} (f : G → G → G) (x y : G) (w : TwoVarWord) :
    evalF f x y (swapVars w) = evalF f y x w := by
  induction w with
  | X => rfl
  | Y => rfl
  | op a b iha ihb => simp [swapVars, evalF, iha, ihb]

theorem occX_swapVars {w : TwoVarWord} (h : occY w) : occX (swapVars w) := by
  induction w with
  | X => exact absurd h not_false
  | Y => trivial
  | op a b iha ihb =>
      rcases h with h | h
      · exact Or.inl (iha h)
      · exact Or.inr (ihb h)

/-- The coefficient polynomial of a word. -/
noncomputable def pz : TwoVarWord → Polynomial ℤ
  | X => 1
  | Y => 0
  | op a b => (1 - Polynomial.X) * pz a + Polynomial.X * pz b

/-- Evaluation of a word in the affine magma on `ZMod k`. -/
theorem evalF_affine {k : ℕ} (c : ℤ) (x y : ZMod k) (w : TwoVarWord) :
    evalF (fun u v : ZMod k => (1 - (c : ZMod k)) * u + (c : ZMod k) * v) x y w
      = (((pz w).eval c : ℤ) : ZMod k) * x + (1 - (((pz w).eval c : ℤ) : ZMod k)) * y := by
  induction w with
  | X => simp [evalF, pz]
  | Y => simp [evalF, pz]
  | op a b iha ihb =>
      simp only [evalF, iha, ihb, pz, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
      push_cast
      ring

/-! ### The value at `c = 1/2` -/

/-- The value of the coefficient polynomial at `1/2`. -/
noncomputable def half (w : TwoVarWord) : ℚ := Polynomial.aeval (1/2 : ℚ) (pz w)

theorem half_op (a b : TwoVarWord) : half (op a b) = (1/2) * half a + (1/2) * half b := by
  simp only [half, pz, map_add, map_mul, map_sub, map_one, Polynomial.aeval_X]
  ring

theorem half_nonneg (w : TwoVarWord) : 0 ≤ half w := by
  induction w with
  | X => simp [half, pz]
  | Y => simp [half, pz]
  | op a b iha ihb => rw [half_op]; linarith

theorem half_le_one (w : TwoVarWord) : half w ≤ 1 := by
  induction w with
  | X => simp [half, pz]
  | Y => simp [half, pz]
  | op a b iha ihb => rw [half_op]; linarith

theorem half_pos {w : TwoVarWord} (h : occX w) : 0 < half w := by
  induction w with
  | X => simp [half, pz]
  | Y => exact absurd h not_false
  | op a b iha ihb =>
      rw [half_op]
      rcases h with h | h
      · have := iha h
        have := half_nonneg b
        linarith
      · have := ihb h
        have := half_nonneg a
        linarith

/-! ### The main theorem -/

/-- If `X` occurs on both sides, the difference of the coefficient polynomials is neither
the constant `1` nor the constant `-1`. -/
theorem pz_sub_ne {s t : TwoVarWord} (hs : occX s) (ht : occX t) :
    pz s - pz t ≠ 1 ∧ pz s - pz t ≠ -1 := by
  have hs1 := half_pos hs
  have ht1 := half_pos ht
  have hs2 := half_le_one s
  have ht2 := half_le_one t
  have hval : (Polynomial.aeval (1/2 : ℚ)) (pz s - pz t) = half s - half t := by
    simp [half, map_sub]
  constructor
  · intro hc
    rw [hc] at hval
    simp at hval
    linarith
  · intro hc
    rw [hc] at hval
    simp at hval
    linarith

/-- Some integer value of the difference polynomial has absolute value different from 1. -/
theorem exists_eval_ne_one {s t : TwoVarWord} (hs : occX s) (ht : occX t) :
    ∃ c : ℤ, (pz s - pz t).eval c ≠ 1 ∧ (pz s - pz t).eval c ≠ -1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := pz_sub_ne hs ht
  set D : Polynomial ℤ := pz s - pz t with hD
  -- one of the two values is attained infinitely often
  have hcover : (Set.univ : Set ℤ) ⊆ {c : ℤ | D.eval c = 1} ∪ {c : ℤ | D.eval c = -1} := by
    intro c _
    by_cases hc : D.eval c = 1
    · exact Or.inl hc
    · exact Or.inr (hcon c hc)
  have huniv : (Set.univ : Set ℤ).Infinite := Set.infinite_univ
  have : {c : ℤ | D.eval c = 1}.Infinite ∨ {c : ℤ | D.eval c = -1}.Infinite := by
    by_contra hb
    push_neg at hb
    obtain ⟨hb1, hb2⟩ := hb
    exact huniv (Set.Finite.subset (hb1.union hb2) hcover)
  rcases this with hinf | hinf
  · have : D - 1 = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot _ (Set.Infinite.mono ?_ hinf)
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      simp [Polynomial.IsRoot, hc]
    exact h1 (by linear_combination (norm := ring_nf) this)
  · have : D + 1 = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot _ (Set.Infinite.mono ?_ hinf)
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      simp [Polynomial.IsRoot, hc]
    exact h2 (by linear_combination (norm := ring_nf) this)

/-- **Austin's finite model theorem** (Theorem 5.4), for a law in two variables in which
the variable `X` occurs on both sides: such a law has a non-trivial finite model. -/
theorem exists_finite_model {s t : TwoVarWord} (hs : occX s) (ht : occX t) :
    ∃ (G : Type) (_ : Mul G), Finite G ∧ ¬ Equation2 G ∧ ∀ x y : G, evalM x y s = evalM x y t := by
  obtain ⟨c, hc1, hc2⟩ := exists_eval_ne_one hs ht
  set m : ℤ := (pz s - pz t).eval c with hm
  set k : ℕ := if m = 0 then 2 else m.natAbs with hk
  have hk2 : 2 ≤ k := by
    rw [hk]
    split_ifs with h
    · omega
    · have : m.natAbs ≠ 1 := by
        intro hcon
        rcases Int.natAbs_eq m with he | he <;> omega
      omega
  haveI : NeZero k := ⟨by omega⟩
  haveI : Fact (1 < k) := ⟨by omega⟩
  have hzero : ((m : ℤ) : ZMod k) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hk]
    split_ifs with h
    · simp [h]
    · simp
  have hkey : (((pz s).eval c : ℤ) : ZMod k) = (((pz t).eval c : ℤ) : ZMod k) := by
    have : (((pz s).eval c - (pz t).eval c : ℤ) : ZMod k) = 0 := by
      rw [← hzero, hm]
      simp
    push_cast at this
    linear_combination (norm := ring_nf) this
  refine ⟨ZMod k, ⟨fun u v => (1 - (c : ZMod k)) * u + (c : ZMod k) * v⟩, Finite.of_fintype _,
    ?_, ?_⟩
  · intro hcon
    exact zero_ne_one (hcon 0 1)
  · intro x y
    show evalF (fun u v : ZMod k => (1 - (c : ZMod k)) * u + (c : ZMod k) * v) x y s
      = evalF (fun u v : ZMod k => (1 - (c : ZMod k)) * u + (c : ZMod k) * v) x y t
    rw [evalF_affine, evalF_affine, hkey]

/-- **Austin's finite model theorem** (Theorem 5.4): a law in two variables that has a
variable occurring on both sides has a non-trivial finite model. -/
theorem exists_finite_model_of_common_var {s t : TwoVarWord}
    (h : (occX s ∧ occX t) ∨ (occY s ∧ occY t)) :
    ∃ (G : Type) (_ : Mul G), Finite G ∧ ¬ Equation2 G ∧
      ∀ x y : G, evalM x y s = evalM x y t := by
  rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact exists_finite_model hs ht
  · obtain ⟨G, inst, hfin, hne, hlaw⟩ :=
      exists_finite_model (occX_swapVars hs) (occX_swapVars ht)
    refine ⟨G, inst, hfin, hne, fun x y => ?_⟩
    have := hlaw y x
    simpa only [evalM, evalF_swapVars] using this

end TwoVarWord

end Austin

import RequestProject.Austin.Defs
import RequestProject.Austin.AustinLaws

/-!
# An infinite model of Kisielewicz's second Austin law (equation 28770)

Equation 28770 is `x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)`.  We build an infinite model on a
syntactic carrier: elements are built from base points by three "tags" recording the shape
of a product, plus a junk element.  The operation is

* `u ◇ u = sq u`;
* `sq t ◇ t = c t`, and `sq (c s) ◇ v = c s` for `v ≠ c s`;
* `c t ◇ v = p t v`;
* `p t x ◇ v = x` (a decoder);
* `junk` otherwise.

Writing `y³ = (y ◇ y) ◇ y = c y`, the element `c y ◇ x` is `p y x`, which decodes back to
`x` against every product `y ◇ z`; the exceptional case `x = c y` is handled by the rule
for `sq (c y)`.  Together with `Austin.Finite.Equation28770_implies_Equation2` this shows
that equation 28770 is an Austin law.  (The model is not the one of Kisielewicz's paper,
which is built inside `ℕ`; the syntactic version is easier to verify.)
-/

namespace Austin

/-- The carrier of the infinite model of equation 28770. -/
inductive Magma28770 where
  | base : ℕ → Magma28770
  | sq : Magma28770 → Magma28770
  | c : Magma28770 → Magma28770
  | p : Magma28770 → Magma28770 → Magma28770
  | junk : Magma28770
deriving DecidableEq

namespace Magma28770

/-- The operation of the infinite model. -/
def op (u v : Magma28770) : Magma28770 :=
  if u = v then sq u
  else
    match u with
    | base _ => junk
    | junk => junk
    | c t => p t v
    | p _ x => x
    | sq t =>
      if v = t then c t
      else
        match t with
        | c s => c s
        | base _ => junk
        | sq _ => junk
        | p _ _ => junk
        | junk => junk

instance : Mul Magma28770 := ⟨op⟩

theorem mul_def (u v : Magma28770) : u * v = op u v := rfl

theorem sq_ne (t : Magma28770) : sq t ≠ t := by
  intro h; have := congrArg sizeOf h; simp at this

theorem c_ne (t : Magma28770) : c t ≠ t := by
  intro h; have := congrArg sizeOf h; simp at this

/-! ### Evaluation lemmas -/

theorem op_self (u : Magma28770) : op u u = sq u := by simp [op]

theorem op_base {n : ℕ} {v : Magma28770} (h : base n ≠ v) : op (base n) v = junk := by
  unfold op; rw [if_neg h]

theorem op_junk {v : Magma28770} (h : junk ≠ v) : op junk v = junk := by
  unfold op; rw [if_neg h]

theorem op_c {t v : Magma28770} (h : c t ≠ v) : op (c t) v = p t v := by
  unfold op; rw [if_neg h]

theorem op_p {t x v : Magma28770} (h : p t x ≠ v) : op (p t x) v = x := by
  unfold op; rw [if_neg h]

theorem op_sq_self (t : Magma28770) : op (sq t) t = c t := by
  unfold op; rw [if_neg (sq_ne t)]; dsimp only; rw [if_pos rfl]

theorem op_sq_c {s v : Magma28770} (h1 : sq (c s) ≠ v) (h2 : v ≠ c s) :
    op (sq (c s)) v = c s := by
  unfold op; rw [if_neg h1]; dsimp only; rw [if_neg h2]

theorem op_sq_base {n : ℕ} {v : Magma28770} (h1 : sq (base n) ≠ v) (h2 : v ≠ base n) :
    op (sq (base n)) v = junk := by
  unfold op; rw [if_neg h1]; dsimp only; rw [if_neg h2]

theorem op_sq_sq {t v : Magma28770} (h1 : sq (sq t) ≠ v) (h2 : v ≠ sq t) :
    op (sq (sq t)) v = junk := by
  unfold op; rw [if_neg h1]; dsimp only; rw [if_neg h2]

theorem op_sq_p {t x v : Magma28770} (h1 : sq (p t x) ≠ v) (h2 : v ≠ p t x) :
    op (sq (p t x)) v = junk := by
  unfold op; rw [if_neg h1]; dsimp only; rw [if_neg h2]

theorem op_sq_junk {v : Magma28770} (h1 : sq junk ≠ v) (h2 : v ≠ junk) :
    op (sq junk) v = junk := by
  unfold op; rw [if_neg h1]; dsimp only; rw [if_neg h2]

/-- The possible shapes of a product. -/
theorem op_spec (y z : Magma28770) :
    op y z = sq y ∨ (∃ t, y = sq t ∧ op y z = c t) ∨
      (∃ s, y = sq (c s) ∧ op y z = c s) ∨
      (∃ t, y = c t ∧ op y z = p t z) ∨
      (∃ t x, y = p t x ∧ op y z = x) ∨ op y z = junk := by
  by_cases h : y = z
  · exact Or.inl (by rw [h, op_self])
  · cases y with
    | base n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (op_base h)))))
    | junk => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (op_junk h)))))
    | c t => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl, op_c h⟩)))
    | p t x => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, x, rfl, op_p h⟩))))
    | sq t =>
        by_cases hz : z = t
        · refine Or.inr (Or.inl ⟨t, rfl, ?_⟩)
          rw [hz, op_sq_self]
        · cases t with
          | c s => exact Or.inr (Or.inr (Or.inl ⟨s, rfl, op_sq_c h hz⟩))
          | base n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (op_sq_base h hz)))))
          | sq t' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (op_sq_sq h hz)))))
          | p t' x' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (op_sq_p h hz)))))
          | junk => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (op_sq_junk h hz)))))

/-! ### The three avoidance facts -/

theorem op_ne_p (y z x : Magma28770) : op y z ≠ p y x := by
  rcases op_spec y z with h | ⟨t, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨t, rfl, h⟩ | ⟨t, x', rfl, h⟩ | h <;>
    rw [h] <;> intro hc
  · exact Magma28770.noConfusion hc
  · exact Magma28770.noConfusion hc
  · exact Magma28770.noConfusion hc
  · injection hc with h1 _
    exact c_ne t h1.symm
  · have := congrArg sizeOf hc; simp at this; omega
  · exact Magma28770.noConfusion hc

theorem op_ne_c (y z : Magma28770) : op y z ≠ c y := by
  rcases op_spec y z with h | ⟨t, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨t, rfl, h⟩ | ⟨t, x', rfl, h⟩ | h <;>
    rw [h] <;> intro hc
  · exact Magma28770.noConfusion hc
  · injection hc with h1
    exact sq_ne t h1.symm
  · injection hc with h1
    have := congrArg sizeOf h1; simp at this; omega
  · exact Magma28770.noConfusion hc
  · have := congrArg sizeOf hc; simp at this; omega
  · exact Magma28770.noConfusion hc

theorem op_ne_sq_c (y z : Magma28770) : op y z ≠ sq (c y) := by
  rcases op_spec y z with h | ⟨t, rfl, h⟩ | ⟨s, rfl, h⟩ | ⟨t, rfl, h⟩ | ⟨t, x', rfl, h⟩ | h <;>
    rw [h] <;> intro hc
  · injection hc with h1
    exact c_ne y h1.symm
  · exact Magma28770.noConfusion hc
  · exact Magma28770.noConfusion hc
  · exact Magma28770.noConfusion hc
  · have := congrArg sizeOf hc; simp at this; omega
  · exact Magma28770.noConfusion hc

/-! ### The model -/

instance : Infinite Magma28770 :=
  Infinite.of_injective base (fun a b hab => by injection hab)

/-- **The syntactic magma is a model of equation 28770.** -/
theorem satisfies_28770 : Equation28770 Magma28770 := by
  intro x y z
  simp only [mul_def]
  rw [op_self, op_sq_self]
  by_cases hx : x = c y
  · rw [hx, op_self]
    exact (op_sq_c (Ne.symm (op_ne_sq_c y z)) (op_ne_c y z)).symm
  · rw [op_c (Ne.symm hx), op_p (Ne.symm (op_ne_p y z x))]

/-- The model is non-trivial. -/
theorem not_Equation2 : ¬ Equation2 Magma28770 := by
  intro h
  have h1 := h (base 0) (base 1)
  injection h1 with h2
  omega

end Magma28770

/-- **Theorem 5.2 (Kisielewicz's second Austin law).**  Equation 28770 is an Austin law:
it has no non-trivial finite models, but it does have an infinite non-trivial model. -/
theorem Equation28770_is_Austin :
    (∀ (M : Type) (_ : Mul M), Finite M → Equation28770 M → Equation2 M) ∧
      ∃ (M : Type) (_ : Mul M), Infinite M ∧ Equation28770 M ∧ ¬ Equation2 M :=
  ⟨fun _M _ _ hM => Finite.Equation28770_implies_Equation2 hM,
    ⟨Magma28770, inferInstance, inferInstance, Magma28770.satisfies_28770,
      Magma28770.not_Equation2⟩⟩

end Austin

import Mathlib

/-!
# Equational laws appearing in the Austin chapter

A *magma* here is simply a type `G` equipped with a binary operation, which we write
multiplicatively (`[Mul G]`).  The equational laws below are the ones occurring in the
chapter on Austin laws and Austin implications of the Equational Theories project; the
numbering is the one used by that project.
-/

namespace Austin

variable (G : Type*) [Mul G]

/-- Equation 2: `x = y`, i.e. the magma has at most one element. -/
def Equation2 : Prop := ∀ x y : G, x = y

/-- Equation 1035: `x = x ◇ ((y ◇ (x ◇ x)) ◇ x)`. -/
def Equation1035 : Prop := ∀ x y : G, x = x * ((y * (x * x)) * x)

/-- Equation 1096: `x = y ◇ ((x ◇ (z ◇ y)) ◇ x)`. -/
def Equation1096 : Prop := ∀ x y z : G, x = y * ((x * (z * y)) * x)

/-- Equation 1133: `x = y ◇ ((y ◇ (z ◇ y)) ◇ x)`. -/
def Equation1133 : Prop := ∀ x y z : G, x = y * ((y * (z * y)) * x)

/-- Equation 1167: `x = y ◇ ((z ◇ (y ◇ y)) ◇ x)`. -/
def Equation1167 : Prop := ∀ x y z : G, x = y * ((z * (y * y)) * x)

/-- Equation 1441: `x = (x ◇ y) ◇ (x ◇ (x ◇ x))`. -/
def Equation1441 : Prop := ∀ x y : G, x = (x * y) * (x * (x * x))

/-- Equation 1443: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`. -/
def Equation1443 : Prop := ∀ x y z : G, x = (x * y) * (x * (x * z))

/-- Equation 1681: `x = (y ◇ x) ◇ ((x ◇ x) ◇ x)`. -/
def Equation1681 : Prop := ∀ x y : G, x = (y * x) * ((x * x) * x)

/-- Equation 1701: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`. -/
def Equation1701 : Prop := ∀ x y z : G, x = (y * x) * ((z * x) * x)

/-- Equation 3055: `x = (((x ◇ x) ◇ y) ◇ x) ◇ x`. -/
def Equation3055 : Prop := ∀ x y : G, x = (((x * x) * y) * x) * x

/-- Equation 3342: `x ◇ y = y ◇ (x ◇ (x ◇ x))`. -/
def Equation3342 : Prop := ∀ x y : G, x * y = y * (x * (x * x))

/-- Equation 3522: `x ◇ y = x ◇ ((y ◇ y) ◇ y)`. -/
def Equation3522 : Prop := ∀ x y : G, x * y = x * ((y * y) * y)

/-- Equation 3588: `x ◇ y = z ◇ ((x ◇ y) ◇ z)`. -/
def Equation3588 : Prop := ∀ x y z : G, x * y = z * ((x * y) * z)

/-- Equation 3877: `x ◇ x = (y ◇ (x ◇ x)) ◇ x`. -/
def Equation3877 : Prop := ∀ x y : G, x * x = (y * (x * x)) * x

/-- Equation 3994: `x ◇ y = (z ◇ (x ◇ y)) ◇ z`. -/
def Equation3994 : Prop := ∀ x y z : G, x * y = (z * (x * y)) * z

/-- Equation 4067: `x ◇ x = ((x ◇ x) ◇ y) ◇ x`. -/
def Equation4067 : Prop := ∀ x y : G, x * x = ((x * x) * y) * x

/-- Equation 4118: `x ◇ y = ((x ◇ x) ◇ x) ◇ y`. -/
def Equation4118 : Prop := ∀ x y : G, x * y = ((x * x) * x) * y

/-- Equation 5093: `x = y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y))))`. -/
def Equation5093 : Prop := ∀ x y z : G, x = y * (y * (y * (x * (z * y))))

/-- Equation 28770 (Kisielewicz's second Austin law):
`x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)`. -/
def Equation28770 : Prop := ∀ x y z : G, x = (((y * y) * y) * x) * (y * z)

/-- Equation 374794 (Kisielewicz's first Austin law):
`x = (((y ◇ y) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ z)`. -/
def Equation374794 : Prop := ∀ x y z : G, x = (((y * y) * y) * x) * ((y * y) * z)

end Austin

import RequestProject.Austin.Defs
import RequestProject.Austin.FiniteLemmas

/-!
# Austin implications: implications valid for finite magmas

Sample implications between equational laws that hold for all *finite* magmas.
-/

namespace Austin

variable {G : Type*} [Mul G]

/-- On a finite type a left inverse is automatically a right inverse. -/
theorem rightInverse_of_leftInverse {X : Type*} [Finite X] {s c : X → X}
    (h : ∀ x, s (c x) = x) : ∀ x, c (s x) = x := by
  have hsurj : Function.Surjective s := fun x => ⟨c x, h x⟩
  have hinj : Function.Injective s := (Finite.injective_iff_surjective (α := X)).2 hsurj
  intro x
  exact hinj (by rw [h])

section Finite

variable [Finite G]

/-! ### 3994 implies 3588 -/

/-- **All finite magmas satisfying equation 3994 satisfy equation 3588.**
For a finite magma the maps `x ↦ z ◇ x` and `x ↦ x ◇ z` are mutually inverse bijections
of the set of products, hence they commute there. -/
theorem Finite.Equation3994_implies_Equation3588 (h : Equation3994 G) : Equation3588 G := by
  intro x y z
  let S : Set G := {s : G | ∃ a b : G, s = a * b}
  let F : S → S := fun s => ⟨z * (s : G), ⟨z, s, rfl⟩⟩
  let R : S → S := fun s => ⟨((s : G) * z), ⟨s, z, rfl⟩⟩
  have hRF : ∀ s : S, R (F s) = s := by
    rintro ⟨s, a, b, rfl⟩
    exact Subtype.ext (h a b z).symm
  have hFsurj : Function.Surjective F :=
    Finite.surjective_of_injective (Function.LeftInverse.injective hRF)
  have hFR : ∀ s : S, F (R s) = s := by
    intro s
    obtain ⟨t, rfl⟩ := hFsurj s
    rw [hRF t]
  exact (congrArg Subtype.val (hFR ⟨x * y, x, y, rfl⟩)).symm

/-! ### 3342 implies 3522 and 4118 -/

section Eq3342

variable (h : Equation3342 G)
include h

omit [Finite G] in
/-- With `f x = x ◇ (x ◇ x)`, equation 3342 gives `f x ◇ f y = x ◇ y`, i.e. `f` is a
homomorphism onto the multiplication. -/
private theorem Eq3342.hom (x y : G) : (x * (x * x)) * (y * (y * y)) = x * y := by
  rw [h x y, h y (x * (x * x))]

omit [Finite G] in
private theorem Eq3342.hom_iterate (n : ℕ) (x y : G) :
    (fun t : G => t * (t * t))^[n] x * (fun t : G => t * (t * t))^[n] y = x * y := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      exact Eq3342.hom h x y

/-- The main computation: there is `n ≥ 1` with `f^[2n] = f^[n]` and
`(x ◇ x) ◇ x = f^[n] x` for all `x`, where `f x = x ◇ (x ◇ x)`. -/
private theorem Eq3342.exists_iterate :
    ∃ n, (fun t : G => t * (t * t))^[2 * n] = (fun t : G => t * (t * t))^[n] ∧
      ∀ x : G, (x * x) * x = (fun t : G => t * (t * t))^[n] x := by
  set f : G → G := fun t : G => t * (t * t) with hf
  obtain ⟨n, hn1, hn⟩ := exists_iterate_two_mul_eq f
  refine ⟨n, hn, ?_⟩
  intro x
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have e1 : (x * x) * x = f^[n' + 1] (x * x) * f^[n' + 1] x :=
    (Eq3342.hom_iterate h (n' + 1) (x * x) x).symm
  have e2 : f^[n' + 1] (x * x) * f^[n' + 1] x
      = f^[n' + 1] (x * x) * f^[2 * (n' + 1)] x := by rw [hn]
  have e3 : f^[n' + 1] (x * x) * f^[2 * (n' + 1)] x
      = f^[2 * (n' + 1)] x * f (f^[n' + 1] (x * x)) := h _ _
  have e4 : f (f^[n' + 1] (x * x)) = f^[n' + 1 + 1] (x * x) :=
    (Function.iterate_succ_apply' f (n' + 1) (x * x)).symm
  have e5 : f^[2 * (n' + 1)] x * f^[n' + 1 + 1] (x * x) = f^[n'] x * (x * x) := by
    have e : f^[n' + 1 + 1] (f^[n'] x) * f^[n' + 1 + 1] (x * x) = f^[n'] x * (x * x) :=
      Eq3342.hom_iterate h (n' + 1 + 1) (f^[n'] x) (x * x)
    rw [← e, ← Function.iterate_add_apply]
    congr 2
    omega
  have e6 : f^[n'] x * (x * x) = f^[n'] x * (f^[n'] x * f^[n'] x) := by
    rw [Eq3342.hom_iterate h n' x x]
  rw [e1, e2, e3, e4, e5, e6]
  exact (Function.iterate_succ_apply' f n' x).symm

/-- **On a finite magma, equation 3342 implies equation 4118.** -/
theorem Finite.Equation3342_implies_Equation4118 : Equation4118 G := by
  obtain ⟨n, hn, hC⟩ := Eq3342.exists_iterate h
  set f : G → G := fun t : G => t * (t * t) with hf
  intro x y
  calc x * y = f^[n] x * f^[n] y := (Eq3342.hom_iterate h n x y).symm
    _ = f^[2 * n] x * f^[n] y := by rw [hn]
    _ = f^[n] (f^[n] x) * f^[n] y := by
        rw [← Function.iterate_add_apply]; congr 2; omega
    _ = f^[n] x * y := Eq3342.hom_iterate h n (f^[n] x) y
    _ = ((x * x) * x) * y := by rw [hC]

/-- **On a finite magma, equation 3342 implies equation 3522.** -/
theorem Finite.Equation3342_implies_Equation3522 : Equation3522 G := by
  obtain ⟨n, hn, hC⟩ := Eq3342.exists_iterate h
  set f : G → G := fun t : G => t * (t * t) with hf
  intro x y
  calc x * y = f^[n] x * f^[n] y := (Eq3342.hom_iterate h n x y).symm
    _ = f^[n] x * f^[2 * n] y := by rw [hn]
    _ = f^[n] x * f^[n] (f^[n] y) := by
        rw [← Function.iterate_add_apply]; congr 2; omega
    _ = x * f^[n] y := Eq3342.hom_iterate h n x (f^[n] y)
    _ = x * ((y * y) * y) := by rw [hC]

end Eq3342

/-! ### 1441 implies 4067, 1443 implies 3055 -/

/-- **On a finite magma, equation 1441 implies equation 4067.** -/
theorem Finite.Equation1441_implies_Equation4067 (h : Equation1441 G) : Equation4067 G := by
  -- `S (C̃ x) = x` where `S x = x ◇ x` and `C̃ x = x ◇ (x ◇ x)`
  have hSC : ∀ x : G, (x * (x * x)) * (x * (x * x)) = x := fun x => (h x (x * x)).symm
  have hCS : ∀ x : G, (x * x) * ((x * x) * (x * x)) = x :=
    rightInverse_of_leftInverse (s := fun t : G => t * t) (c := fun t : G => t * (t * t)) hSC
  intro x y
  have hx := h (x * x) y
  rw [hCS x] at hx
  exact hx

/-- **On a finite magma, equation 1443 implies equation 3055.** -/
theorem Finite.Equation1443_implies_Equation3055 (h : Equation1443 G) : Equation3055 G := by
  have h1441 : Equation1441 G := fun x y => h x y x
  have h4067 := Finite.Equation1441_implies_Equation4067 h1441
  have hSC : ∀ x : G, (x * (x * x)) * (x * (x * x)) = x := fun x => (h1441 x (x * x)).symm
  have hCS : ∀ x : G, (x * x) * ((x * x) * (x * x)) = x :=
    rightInverse_of_leftInverse (s := fun t : G => t * t) (c := fun t : G => t * (t * t)) hSC
  have hSinj : Function.Injective (fun t : G => t * t) :=
    (Finite.injective_iff_surjective (α := G)).2 (fun x => ⟨x * (x * x), hSC x⟩)
  -- `x ◇ (x ◇ z) = C̃ x`
  have hkey : ∀ x z : G, x * (x * z) = x * (x * x) := by
    intro x z
    refine hSinj ?_
    show (x * (x * z)) * (x * (x * z)) = (x * (x * x)) * (x * (x * x))
    rw [hSC x, ← h x (x * z) z]
  -- `x ◇ C̃ x = C̃ x`, hence `(x ◇ x) ◇ x = x`
  have hfix : ∀ x : G, (x * x) * x = x := by
    intro x
    have hx := hkey (x * x) ((x * x) * (x * x))
    rw [hCS x] at hx
    exact hx
  intro x y
  rw [← h4067 x y, hfix x]

/-! ### 1681 implies 3877, 1701 implies 1035 -/

/-- **On a finite magma, equation 1681 implies equation 3877.** -/
theorem Finite.Equation1681_implies_Equation3877 (h : Equation1681 G) : Equation3877 G := by
  -- `S (C x) = x` where `C x = (x ◇ x) ◇ x`
  have hSC : ∀ x : G, ((x * x) * x) * ((x * x) * x) = x := fun x => (h x (x * x)).symm
  have hCS : ∀ x : G, ((x * x) * (x * x)) * (x * x) = x :=
    rightInverse_of_leftInverse (s := fun t : G => t * t) (c := fun t : G => (t * t) * t) hSC
  intro x y
  have hx := h (x * x) y
  rw [hCS x] at hx
  exact hx

/-- **On a finite magma, equation 1701 implies equation 1035.** -/
theorem Finite.Equation1701_implies_Equation1035 (h : Equation1701 G) : Equation1035 G := by
  have h1681 : Equation1681 G := fun x y => h x y x
  have h3877 := Finite.Equation1681_implies_Equation3877 h1681
  have hSC : ∀ x : G, ((x * x) * x) * ((x * x) * x) = x := fun x => (h1681 x (x * x)).symm
  have hCS : ∀ x : G, ((x * x) * (x * x)) * (x * x) = x :=
    rightInverse_of_leftInverse (s := fun t : G => t * t) (c := fun t : G => (t * t) * t) hSC
  have hSinj : Function.Injective (fun t : G => t * t) :=
    (Finite.injective_iff_surjective (α := G)).2 (fun x => ⟨(x * x) * x, hSC x⟩)
  -- `(z ◇ x) ◇ x = C x`
  have hkey : ∀ x z : G, (z * x) * x = (x * x) * x := by
    intro x z
    refine hSinj ?_
    show ((z * x) * x) * ((z * x) * x) = ((x * x) * x) * ((x * x) * x)
    rw [hSC x, ← h x (z * x) z]
  -- `C x ◇ x = C x`, hence `x ◇ (x ◇ x) = x`
  have hfix : ∀ x : G, x * (x * x) = x := by
    intro x
    have hx := hkey (x * x) ((x * x) * (x * x))
    rw [hCS x] at hx
    exact hx
  intro x y
  rw [← h3877 x y, hfix x]

end Finite

end Austin

import RequestProject.Austin.Defs

/-!
# An infinite magma satisfying equation 3994 but not equation 3588

Proposition 5.9.  On `ℕ` define
`x ◇ y = x ^^^ y` (bitwise xor) if `x` and `y` are both even, `y + 2` if only `y` is even,
`x - 2` (truncated subtraction) if only `x` is even, and `0` if both are odd.
This magma satisfies equation 3994 but not equation 3588; in particular the finite
implication of Proposition 5.8 fails for infinite magmas.
-/

namespace Austin

/-- The operation of the counterexample magma. -/
def xorOp (x y : ℕ) : ℕ :=
  if x % 2 = 0 then (if y % 2 = 0 then x ^^^ y else x - 2)
  else (if y % 2 = 0 then y + 2 else 0)

theorem xorOp_ee {x y : ℕ} (hx : x % 2 = 0) (hy : y % 2 = 0) : xorOp x y = x ^^^ y := by
  unfold xorOp; simp [hx, hy]

theorem xorOp_eo {x y : ℕ} (hx : x % 2 = 0) (hy : y % 2 ≠ 0) : xorOp x y = x - 2 := by
  unfold xorOp; simp [hx, hy]

theorem xorOp_oe {x y : ℕ} (hx : x % 2 ≠ 0) (hy : y % 2 = 0) : xorOp x y = y + 2 := by
  unfold xorOp; simp [hx, hy]

theorem xorOp_oo {x y : ℕ} (hx : x % 2 ≠ 0) (hy : y % 2 ≠ 0) : xorOp x y = 0 := by
  unfold xorOp; simp [hx, hy]

/-- Every product is even. -/
theorem xorOp_mod_two (x y : ℕ) : xorOp x y % 2 = 0 := by
  unfold xorOp
  split_ifs with h1 h2 h2
  · simp
    omega
  · omega
  · omega
  · rfl

/-- For even `w`, the maps `u ↦ z ◇ u` and `u ↦ u ◇ z` undo each other. -/
theorem xorOp_key (z w : ℕ) (hw : w % 2 = 0) : xorOp (xorOp z w) z = w := by
  by_cases hz : z % 2 = 0
  · have h2 : (z ^^^ w) % 2 = 0 := by simp; omega
    rw [xorOp_ee hz hw, xorOp_ee h2 hz, Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self,
      Nat.zero_xor]
  · have h2 : (w + 2) % 2 = 0 := by omega
    rw [xorOp_oe hz hw, xorOp_eo h2 hz]
    omega

/-- The carrier of the counterexample magma: the natural numbers. -/
def XorMagma : Type := ℕ

instance : Mul XorMagma := ⟨xorOp⟩

instance : Infinite XorMagma := inferInstanceAs (Infinite ℕ)

/-- The element of `XorMagma` given by a natural number. -/
def XorMagma.mk (n : ℕ) : XorMagma := n

theorem XorMagma.mul_def (x y : XorMagma) : x * y = xorOp x y := rfl

/-- The magma satisfies equation 3994. -/
theorem XorMagma.satisfies_3994 : Equation3994 XorMagma := by
  intro x y z
  show xorOp x y = xorOp (xorOp z (xorOp x y)) z
  exact (xorOp_key z (xorOp x y) (xorOp_mod_two x y)).symm

/-- The magma does not satisfy equation 3588. -/
theorem XorMagma.not_satisfies_3588 : ¬ Equation3588 XorMagma := by
  intro h
  have h1 : xorOp 1 1 = xorOp 1 (xorOp (xorOp 1 1) 1) :=
    h (XorMagma.mk 1) (XorMagma.mk 1) (XorMagma.mk 1)
  exact absurd h1 (by decide)

/-- **Proposition 5.9.**  There is a magma satisfying equation 3994 but not
equation 3588 (necessarily infinite, by Proposition 5.8). -/
theorem Equation3994_not_implies_Equation3588 :
    ∃ (M : Type) (_ : Mul M), Equation3994 M ∧ ¬ Equation3588 M :=
  ⟨XorMagma, inferInstance, XorMagma.satisfies_3994, XorMagma.not_satisfies_3588⟩

end Austin

import RequestProject.Austin.Defs
import RequestProject.Austin.FiniteLemmas

/-!
# Austin laws: laws with no non-trivial finite models

An *Austin law* is a law admitting infinite models but no non-trivial finite ones.
Here we prove the "no non-trivial finite model" halves for Kisielewicz's two Austin laws
(equations 374794 and 28770) and for equation 5093.
-/

namespace Austin

variable {G : Type*} [Mul G] [Finite G]

/-- **Equation 5093 has no non-trivial finite models.**  Every finite magma satisfying
`x = y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y))))` satisfies `x = y`. -/
theorem Finite.Equation5093_implies_Equation2 (h : Equation5093 G) : Equation2 G := by
  -- for each `y`, left multiplication by `y` is surjective, hence injective
  have hLinj : ∀ y : G, Function.Injective (fun w : G => y * w) := by
    intro y
    refine (Finite.injective_iff_surjective (α := G)).2 ?_
    intro x
    exact ⟨y * (y * (x * (x * y))), (h x y x).symm⟩
  -- consequently `z ◇ y` does not depend on `z`
  have hconst : ∀ y z z' : G, z * y = z' * y := by
    intro y z z'
    have h1 : y * (y * (y * (y * (z * y)))) = y * (y * (y * (y * (z' * y)))) := by
      rw [← h y y z, ← h y y z']
    have h2 := hLinj y h1
    have h3 := hLinj y h2
    have h4 := hLinj y h3
    exact hLinj y h4
  intro x x'
  calc x = x * (x * (x * (x * (x * x)))) := h x x x
    _ = x * (x * (x * (x' * (x * x)))) := by rw [hconst (x * x) x x']
    _ = x' := (h x' x x).symm

/-- **Kisielewicz's second Austin law has no non-trivial finite models.**  Every finite
magma satisfying equation 28770, `x = (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z)`, satisfies `x = y`. -/
theorem Finite.Equation28770_implies_Equation2 (h : Equation28770 G) : Equation2 G := by
  -- `T y : x ↦ y³ ◇ x` is injective
  have hTinj : ∀ y : G, Function.Injective (fun x : G => ((y * y) * y) * x) := by
    intro y a b hab
    simp only at hab
    rw [h a y y, h b y y, hab]
  -- hence surjective, so `y³` has a preimage
  have hTsurj : ∀ y : G, Function.Surjective (fun x : G => ((y * y) * y) * x) :=
    fun y => Finite.surjective_of_injective (hTinj y)
  -- `y ◇ z` does not depend on `z`
  have hconst : ∀ y z z' : G, y * z = y * z' := by
    intro y z z'
    obtain ⟨w, hw⟩ := hTsurj y ((y * y) * y)
    simp only at hw
    have e1 : ∀ t : G, ((y * y) * y) * (y * t) = w := by
      intro t
      rw [← hw]
      exact (h w y t).symm
    exact hTinj y (by simp only; rw [e1 z, e1 z'])
  intro x x'
  calc x = (((x * x) * x) * x) * (x * x) := h x x x
    _ = (((x * x) * x) * x') * (x * x) := by rw [hconst ((x * x) * x) x x']
    _ = x' := (h x' x x).symm

/-- **Kisielewicz's first Austin law has no non-trivial finite models.**  Every finite
magma satisfying equation 374794, `x = (((y ◇ y) ◇ y) ◇ x) ◇ ((y ◇ y) ◇ z)`,
satisfies `x = y`. -/
theorem Finite.Equation374794_implies_Equation2 (h : Equation374794 G) : Equation2 G := by
  -- `f y : x ↦ y³ ◇ x` is injective
  have hfinj : ∀ y : G, Function.Injective (fun x : G => ((y * y) * y) * x) := by
    intro y a b hab
    simp only at hab
    rw [h a y y, h b y y, hab]
  have hfsurj : ∀ y : G, Function.Surjective (fun x : G => ((y * y) * y) * x) :=
    fun y => Finite.surjective_of_injective (hfinj y)
  -- `y² ◇ z` does not depend on `z`
  have hsq : ∀ y z z' : G, (y * y) * z = (y * y) * z' := by
    intro y z z'
    obtain ⟨w, hw⟩ := hfsurj y ((y * y) * y)
    simp only at hw
    have e1 : ∀ t : G, ((y * y) * y) * ((y * y) * t) = w := by
      intro t
      rw [← hw]
      exact (h w y t).symm
    exact hfinj y (by simp only; rw [e1 z, e1 z'])
  intro x x'
  -- `y³ = y² ◇ y = y² ◇ y²`, so `f y` is a constant function; being injective, the
  -- magma has at most one element
  refine hfinj x ?_
  simp only
  rw [hsq x x (x * x), hsq (x * x) x x']
end Austin

import RequestProject.Austin.Defs
import RequestProject.Austin.AustinLaws

/-!
# An infinite model of Kisielewicz's first Austin law (equation 374794)

Following Kisielewicz, we equip the positive integers with the operation

`x ◇ y = 2^y` if `x = y`; `3^y` if `x = 1` and `y ≠ 1`; `z` if `x = 3^z` and `y ≠ x`;
and `1` otherwise,

and check that it is a model of equation 374794.  Combined with
`Austin.Finite.Equation374794_implies_Equation2`, this shows that equation 374794 is an
Austin law: it has infinite non-trivial models but no finite ones.
-/

namespace Austin

/-- The operation of Kisielewicz's infinite model, as a function on `ℕ`. -/
def op374 (x y : ℕ) : ℕ :=
  if x = y then 2 ^ y
  else if x = 1 then 3 ^ y
  else if 3 ^ (Nat.log 3 x) = x then Nat.log 3 x
  else 1

theorem op374_pos (x y : ℕ) : 0 < op374 x y := by
  unfold op374
  split_ifs with h1 h2 h3
  · positivity
  · positivity
  · -- `x = 3 ^ (log 3 x)` and `x ≠ 1`, so the logarithm is positive
    rcases Nat.eq_zero_or_pos (Nat.log 3 x) with h | h
    · exfalso; rw [h] at h3; simp at h3; omega
    · exact h
  · norm_num

/-- A power of three is never a positive power of two. -/
theorem pow3_ne_pow2 {y : ℕ} (hy : 1 ≤ y) (k : ℕ) : 3 ^ k ≠ 2 ^ y := by
  intro hc
  have h1 : 3 ^ k % 2 = 1 := by rw [Nat.pow_mod]; simp
  have h2 : 2 ^ y % 2 = 0 := by
    rw [Nat.pow_mod]
    simp [Nat.zero_pow (by omega : 0 < y)]
  omega

theorem op374_self (y : ℕ) : op374 y y = 2 ^ y := by
  unfold op374; simp

theorem op374_pow2_self {y : ℕ} (hy : 1 ≤ y) : op374 (2 ^ y) y = 1 := by
  have hne : 2 ^ y ≠ y := by
    have := Nat.lt_two_pow_self (n := y)
    omega
  have h1 : (2 : ℕ) ^ y ≠ 1 := by
    have : (1 : ℕ) < 2 ^ y := Nat.one_lt_two_pow_iff.2 (by omega)
    omega
  unfold op374
  rw [if_neg hne, if_neg h1, if_neg (pow3_ne_pow2 hy _)]

theorem op374_one_ne {x : ℕ} (hx : x ≠ 1) : op374 1 x = 3 ^ x := by
  unfold op374
  rw [if_neg (by omega : ¬ (1 = x)), if_pos rfl]

theorem op374_one_one : op374 1 1 = 2 := by
  unfold op374; simp

/-- The possible values of `(y ◇ y) ◇ z`. -/
theorem op374_pow2 {y : ℕ} (hy : 1 ≤ y) (z : ℕ) :
    op374 (2 ^ y) z = 2 ^ z ∧ z = 2 ^ y ∨ op374 (2 ^ y) z = 1 := by
  by_cases hz : 2 ^ y = z
  · left
    subst hz
    exact ⟨op374_self _, rfl⟩
  · right
    have h1 : (2 : ℕ) ^ y ≠ 1 := by
      have : (1 : ℕ) < 2 ^ y := Nat.one_lt_two_pow_iff.2 (by omega)
      omega
    unfold op374
    rw [if_neg hz, if_neg h1, if_neg (pow3_ne_pow2 hy _)]

/-- `(y ◇ y) ◇ z` is never equal to `2`. -/
theorem op374_pow2_ne_two {y : ℕ} (hy : 1 ≤ y) (z : ℕ) : op374 (2 ^ y) z ≠ 2 := by
  rcases op374_pow2 hy z with ⟨he, hz⟩ | he
  · rw [he]
    have hy2 : 2 ≤ z := by
      rw [hz]
      calc (2 : ℕ) = 2 ^ 1 := rfl
        _ ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hy
    have : (2 : ℕ) ^ 2 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hy2
    omega
  · omega

/-- Multiplying by `3 ^ x` on the left recovers `x`. -/
theorem op374_pow3 {x : ℕ} (hx : 1 ≤ x) {w : ℕ} (hw1 : w = 1 ∨ ∃ k, 1 ≤ k ∧ w = 2 ^ k) :
    op374 (3 ^ x) w = x := by
  have hne1 : (3 : ℕ) ^ x ≠ 1 := by
    have : (1 : ℕ) < 3 ^ x := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hnew : 3 ^ x ≠ w := by
    rcases hw1 with rfl | ⟨k, hk, rfl⟩
    · exact hne1
    · exact pow3_ne_pow2 hk x
  unfold op374
  rw [if_neg hnew, if_neg hne1, Nat.log_pow (by norm_num), if_pos rfl]

/-- Multiplying by `2` on the left of such a `w` gives `1`. -/
theorem op374_two {w : ℕ} (hw : w ≠ 2) : op374 2 w = 1 := by
  have hlog : Nat.log 3 2 = 0 := Nat.log_eq_zero_iff.2 (by norm_num)
  unfold op374
  rw [if_neg (by omega : ¬ (2 = w)), if_neg (by norm_num : (2 : ℕ) ≠ 1), hlog]
  norm_num

/-- The carrier of Kisielewicz's infinite model: the positive integers. -/
def Magma374 : Type := {n : ℕ // 0 < n}

instance : Mul Magma374 := ⟨fun x y => ⟨op374 x.1 y.1, op374_pos _ _⟩⟩

instance : Infinite Magma374 :=
  Infinite.of_injective (fun n : ℕ => (⟨n + 1, Nat.succ_pos n⟩ : Magma374))
    (fun a b hab => by
      have := congrArg Subtype.val hab
      simpa using this)

theorem Magma374.mul_val (x y : Magma374) : (x * y).1 = op374 x.1 y.1 := rfl

/-- **The positive integers with Kisielewicz's operation model equation 374794.** -/
theorem Magma374.satisfies_374794 : Equation374794 Magma374 := by
  intro x y z
  refine Subtype.ext ?_
  have hy : 1 ≤ y.1 := y.2
  have hx : 1 ≤ x.1 := x.2
  simp only [Magma374.mul_val]
  -- `(y ◇ y) ◇ y = 1`
  have hA : op374 (op374 y.1 y.1) y.1 = 1 := by
    rw [op374_self, op374_pow2_self hy]
  -- the possible values of `w = (y ◇ y) ◇ z`
  have hw : op374 (op374 y.1 y.1) z.1 = 1 ∨
      ∃ k, 1 ≤ k ∧ op374 (op374 y.1 y.1) z.1 = 2 ^ k := by
    rw [op374_self]
    rcases op374_pow2 hy z.1 with ⟨he, hz⟩ | he
    · refine Or.inr ⟨z.1, ?_, he⟩
      rw [hz]
      calc (1 : ℕ) ≤ 2 ^ 0 := by norm_num
        _ ≤ 2 ^ y.1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact Or.inl he
  have hwne : op374 (op374 y.1 y.1) z.1 ≠ 2 := by
    rw [op374_self]
    exact op374_pow2_ne_two hy z.1
  rw [hA]
  by_cases hx1 : x.1 = 1
  · rw [hx1, op374_one_one, op374_two hwne]
  · rw [op374_one_ne hx1, op374_pow3 hx hw]

/-- The model is non-trivial. -/
theorem Magma374.not_Equation2 : ¬ Equation2 Magma374 := by
  intro h
  have := h ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
  have h2 := congrArg Subtype.val this
  simp at h2

/-- **Theorem 5.1 (Kisielewicz's first Austin law).**  Equation 374794 is an Austin law:
it has no non-trivial finite models, but it does have an infinite non-trivial model. -/
theorem Equation374794_is_Austin :
    (∀ (M : Type) (_ : Mul M), Finite M → Equation374794 M → Equation2 M) ∧
      ∃ (M : Type) (_ : Mul M), Infinite M ∧ Equation374794 M ∧ ¬ Equation2 M := by
  refine ⟨fun M _ _ hM => Finite.Equation374794_implies_Equation2 hM,
    ⟨Magma374, inferInstance, inferInstance, Magma374.satisfies_374794,
      Magma374.not_Equation2⟩⟩

end Austin

