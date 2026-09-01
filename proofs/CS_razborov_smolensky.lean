/-
The circuit class `AC⁰[q]`: constant-depth, polynomial-size circuits with unbounded
fan-in AND, OR and MOD_q gates (and free NOT gates).
-/
import RequestProject.Smolensky

namespace CS

open Finset

/-- `InAC0Mod q n d s f` says that the Boolean function `f` on `n` bits is computed by a
circuit of depth at most `d` and size at most `s` built from unbounded fan-in AND, OR and
`MOD q` gates, together with NOT gates (which are free, as usual).  Size is the number of
gates and depth is the number of levels of AND/OR/MOD gates.

(For a fixed depth, polynomial-size circuits with sharing unfold into polynomial-size
formulas, so this tree-shaped model captures the class `AC⁰[q]`.) -/
inductive InAC0Mod (q : ℕ) : (n : ℕ) → ℕ → ℕ → ((Fin n → Bool) → Bool) → Prop
  | var {n : ℕ} (i : Fin n) : InAC0Mod q n 0 1 (fun x => x i)
  | const {n : ℕ} (b : Bool) : InAC0Mod q n 0 1 (fun _ => b)
  | neg {n d s : ℕ} {f : (Fin n → Bool) → Bool} :
      InAC0Mod q n d s f → InAC0Mod q n d s (fun x => !f x)
  | weaken {n d s d' s' : ℕ} {f : (Fin n → Bool) → Bool} :
      InAC0Mod q n d s f → d ≤ d' → s ≤ s' → InAC0Mod q n d' s' f
  | and {n d m : ℕ} {g : Fin m → (Fin n → Bool) → Bool} {sz : Fin m → ℕ} :
      (∀ j, InAC0Mod q n d (sz j) (g j)) →
      InAC0Mod q n (d + 1) (1 + ∑ j, sz j) (fun x => decide (∀ j, g j x = true))
  | or {n d m : ℕ} {g : Fin m → (Fin n → Bool) → Bool} {sz : Fin m → ℕ} :
      (∀ j, InAC0Mod q n d (sz j) (g j)) →
      InAC0Mod q n (d + 1) (1 + ∑ j, sz j) (fun x => decide (∃ j, g j x = true))
  | modq {n d m : ℕ} {g : Fin m → (Fin n → Bool) → Bool} {sz : Fin m → ℕ} :
      (∀ j, InAC0Mod q n d (sz j) (g j)) →
      InAC0Mod q n (d + 1) (1 + ∑ j, sz j)
        (fun x => decide (¬ (q ∣ (Finset.univ.filter (fun j => g j x = true)).card)))

/-- Substituting variables and constants for the inputs of a circuit. -/
theorem InAC0Mod.subst {q m n d s : ℕ} {f : (Fin m → Bool) → Bool}
    (h : InAC0Mod q m d s f) (e : Fin m → Fin n ⊕ Bool) :
    InAC0Mod q n d s (fun x => f (fun i => Sum.elim (fun k => x k) id (e i))) := by
  induction h with
  | var i =>
      rcases hi : e i with k | b
      · simpa [hi] using InAC0Mod.var (q := q) k
      · simpa [hi] using InAC0Mod.const (q := q) (n := n) b
  | const b => exact InAC0Mod.const b
  | neg _ ih => exact ih.neg
  | weaken _ hd hs ih => exact ih.weaken hd hs
  | and _ ih => exact InAC0Mod.and (fun j => ih j)
  | or _ ih => exact InAC0Mod.or (fun j => ih j)
  | modq _ ih => exact InAC0Mod.modq (fun j => ih j)

/-- The `MOD p` function on `n` bits: it is `true` iff the number of ones is *not*
divisible by `p`. -/
def MODfn (p n : ℕ) : (Fin n → Bool) → Bool := fun x => decide (¬ (p ∣ wt x))

/-- Extending a Boolean vector by `j` ones and `k - j` zeros adds `j` to its weight. -/
lemma wt_extend (n k j : ℕ) (hj : j ≤ k) (x : Fin n → Bool) :
    wt (fun i : Fin (n + k) => if h : (i : ℕ) < n then x ⟨i, h⟩ else decide ((i : ℕ) < n + j))
      = wt x + j := by
  classical
  simp only [wt, Finset.card_filter]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Fin.castAdd, Fin.castLE]
  · have : ∀ i : Fin k, (if (if h : ((Fin.natAdd n i : Fin (n+k)) : ℕ) < n then
        x ⟨_, h⟩ else decide (((Fin.natAdd n i : Fin (n+k)) : ℕ) < n + j)) = true then 1 else 0)
        = (if (i : ℕ) < j then 1 else 0) := by
      intro i
      simp only [Fin.natAdd]
      by_cases h2 : (i : ℕ) < j <;> simp [h2]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then 1 else 0)]
    rw [← Finset.card_filter]
    have : (Finset.range k).filter (fun i => i < j) = Finset.range j := by
      ext i; simp [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]

end CS

/-
Low-degree functions on the Boolean cube, as a filtration of the algebra of all
`F`-valued functions on `Fin n → Bool` by spans of multilinear monomials.
-/
import Mathlib

namespace CS

open Finset Module

variable {F : Type*} [Field F] {n : ℕ}

/-- A Boolean value as an element of `F`. -/
def bitv (F : Type*) [Field F] (b : Bool) : F := if b = true then 1 else 0

@[simp] lemma bitv_true : bitv F true = 1 := rfl
@[simp] lemma bitv_false : bitv F false = 0 := rfl

lemma bitv_eq_zero_iff (b : Bool) : bitv F b = 0 ↔ b = false := by
  cases b <;> simp [bitv]

lemma bitv_ne (b b' : Bool) (h : b ≠ b') : bitv F b ≠ bitv F b' := by
  cases b <;> cases b' <;> simp_all [bitv]

lemma prod_ite_one_zero {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∏ i ∈ s, (if p i then (1 : F) else 0) = if ∀ i ∈ s, p i then 1 else 0 := by
  by_cases h : ∀ i ∈ s, p i
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i hi => if_pos (h i hi))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hpi⟩ := h
    exact Finset.prod_eq_zero hi (if_neg hpi)

/-- The multilinear monomial `∏_{i ∈ T} x_i`, viewed as an `F`-valued function on the
Boolean cube `Fin n → Bool`. -/
def mono (F : Type*) [Field F] {n : ℕ} (T : Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => if ∀ i ∈ T, x i then 1 else 0

@[simp] lemma mono_empty : mono F (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mono]

private lemma ite_one_mul_ite_one (A B : Prop) [Decidable A] [Decidable B] :
    (if A then (1 : F) else 0) * (if B then (1 : F) else 0) = if A ∧ B then 1 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma mono_mul (T T' : Finset (Fin n)) : mono F T * mono F T' = mono F (T ∪ T') := by
  funext x
  have hU : (∀ i ∈ T ∪ T', x i = true) ↔ ((∀ i ∈ T, x i = true) ∧ (∀ i ∈ T', x i = true)) := by
    simp [Finset.mem_union, or_imp, forall_and]
  show (if ∀ i ∈ T, x i = true then (1 : F) else 0) *
      (if ∀ i ∈ T', x i = true then (1 : F) else 0) = _
  rw [ite_one_mul_ite_one]
  exact if_congr hU.symm rfl rfl

lemma mono_prod_singleton (T : Finset (Fin n)) :
    ∏ i ∈ T, mono F ({i} : Finset (Fin n)) = mono F T := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, mono_mul, Finset.singleton_union]

/-- The space of functions on the cube of "degree at most `D`": the span of the
multilinear monomials of degree at most `D`. -/
def Deg (F : Type*) [Field F] (n D : ℕ) : Submodule F ((Fin n → Bool) → F) :=
  Submodule.span F (Set.range (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono F T.1))

lemma mono_mem_Deg {T : Finset (Fin n)} {D : ℕ} (h : T.card ≤ D) : mono F T ∈ Deg F n D :=
  Submodule.subset_span ⟨⟨T, h⟩, rfl⟩

lemma Deg_mono {D D' : ℕ} (h : D ≤ D') : Deg F n D ≤ Deg F n D' := by
  rw [Deg, Submodule.span_le]
  rintro f ⟨T, rfl⟩
  exact mono_mem_Deg (le_trans T.2 h)

lemma Deg_le_max (D : ℕ) : Deg F n D ≤ Deg F n n := by
  rw [Deg, Submodule.span_le]
  rintro f ⟨T, rfl⟩
  exact mono_mem_Deg (by simpa using Finset.card_le_univ T.1)

lemma one_mem_Deg (D : ℕ) : (1 : (Fin n → Bool) → F) ∈ Deg F n D := by
  have := mono_mem_Deg (F := F) (T := (∅ : Finset (Fin n))) (D := D) (by simp)
  simpa using this

lemma Deg_mul {a b : ℕ} {f g : (Fin n → Bool) → F} (hf : f ∈ Deg F n a) (hg : g ∈ Deg F n b) :
    f * g ∈ Deg F n (a + b) := by
  have hmul : Deg F n a * Deg F n b ≤ Deg F n (a + b) := by
    rw [Deg, Deg, Submodule.span_mul_span, Submodule.span_le]
    rintro f ⟨x, ⟨T, rfl⟩, y, ⟨T', rfl⟩, rfl⟩
    have h : mono F (T.1 ∪ T'.1) ∈ Deg F n (a + b) :=
      mono_mem_Deg (le_trans (Finset.card_union_le _ _) (Nat.add_le_add T.2 T'.2))
    rw [← mono_mul] at h
    exact h
  exact hmul (Submodule.mul_mem_mul hf hg)

lemma Deg_pow {A t : ℕ} {f : (Fin n → Bool) → F} (hf : f ∈ Deg F n A) :
    f ^ t ∈ Deg F n (t * A) := by
  induction t with
  | zero => simpa using one_mem_Deg 0
  | succ t ih =>
      rw [pow_succ, Nat.succ_mul]
      exact Deg_mul ih hf

lemma Deg_prod {ι : Type*} (s : Finset ι) (f : ι → (Fin n → Bool) → F) (D : ℕ)
    (h : ∀ j ∈ s, f j ∈ Deg F n D) : ∏ j ∈ s, f j ∈ Deg F n (s.card * D) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, Nat.zero_mul]
      exact one_mem_Deg 0
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_mul, one_mul, add_comm]
      exact Deg_mul (h a (Finset.mem_insert_self a s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Every function on the cube has degree at most `n`. -/
lemma Deg_top : Deg F n n = ⊤ := by
  classical
  -- first: `Deg F n n` is closed under multiplication
  have hmul : ∀ {f g : (Fin n → Bool) → F}, f ∈ Deg F n n → g ∈ Deg F n n →
      f * g ∈ Deg F n n := fun hf hg => Deg_le_max _ (Deg_mul hf hg)
  -- the indicator of a point lies in `Deg F n n`
  have hdelta : ∀ x₀ : Fin n → Bool,
      (fun x => if x = x₀ then (1 : F) else 0) ∈ Deg F n n := by
    intro x₀
    have key : (fun x => if x = x₀ then (1 : F) else 0) =
        ∏ i : Fin n, (fun x : Fin n → Bool =>
          if x i = x₀ i then (1 : F) else 0) := by
      funext x
      rw [Finset.prod_apply]
      by_cases h : x = x₀
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ x₀ i := by
          by_contra hc
          exact h (funext (by simpa using hc))
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    rw [key]
    refine Finset.prod_induction
      (fun i => (fun x : Fin n → Bool => if x i = x₀ i then (1 : F) else 0))
      (· ∈ Deg F n n) (fun a b => hmul) (one_mem_Deg n) ?_
    intro i _
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    change (fun x : Fin n → Bool => if x i = x₀ i then (1 : F) else 0) ∈ Deg F n n
    by_cases hb : x₀ i = true
    · have : (fun x : Fin n → Bool => if x i = x₀ i then (1 : F) else 0)
          = mono F ({i} : Finset (Fin n)) := by
        funext x; simp [mono, hb]
      rw [this]
      exact mono_mem_Deg (by simpa using hn)
    · have hb' : x₀ i = false := by simpa using hb
      have : (fun x : Fin n → Bool => if x i = x₀ i then (1 : F) else 0)
          = 1 - mono F ({i} : Finset (Fin n)) := by
        funext x
        by_cases hx : x i = true <;> simp [mono, hb', hx]
      rw [this]
      refine Submodule.sub_mem _ (one_mem_Deg n) ?_
      exact mono_mem_Deg (by simpa using hn)
  refine Submodule.eq_top_iff'.2 ?_
  intro f
  have : f = ∑ x₀ : Fin n → Bool, f x₀ • (fun x => if x = x₀ then (1 : F) else 0) := by
    funext x
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [this]
  exact Submodule.sum_mem _ (fun x₀ _ => Submodule.smul_mem _ _ (hdelta x₀))

lemma finrank_Deg_le (D : ℕ) :
    finrank F (Deg F n D) ≤ Fintype.card {T : Finset (Fin n) // T.card ≤ D} := by
  classical
  rw [Deg, ← Fintype.range_linearCombination]
  simpa using LinearMap.finrank_range_le
    (Fintype.linearCombination F (fun T : {T : Finset (Fin n) // T.card ≤ D} => mono F T.1))

end CS

/-
Smolensky's counting argument: if the function `x ↦ ζ ^ (weight x)` agrees on a set `S`
with a function of degree `≤ D`, then `S` is small.
-/
import RequestProject.Degree

namespace CS

open Finset Module

variable {F : Type*} [Field F] {n : ℕ}

/-- Hamming weight of a point of the Boolean cube. -/
def wt {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

section
variable (F)
/-- `yfun ζ i` is the function `x ↦ ζ ^ (x i)`, i.e. `ζ` if the `i`-th bit is set and `1`
otherwise. -/
def yfun (zeta : F) (i : Fin n) : (Fin n → Bool) → F := fun x => if x i = true then zeta else 1
end

lemma yfun_mem_Deg (zeta : F) (i : Fin n) : yfun F zeta i ∈ Deg F n 1 := by
  have h : yfun F zeta i = 1 + (zeta - 1) • mono F ({i} : Finset (Fin n)) := by
    funext x
    by_cases hx : x i = true <;> simp [yfun, mono, hx]
  rw [h]
  exact Submodule.add_mem _ (one_mem_Deg 1) (Submodule.smul_mem _ _ (mono_mem_Deg (by simp)))

lemma yfun_mul_inv (zeta : F) (hz0 : zeta ≠ 0) (i : Fin n) :
    yfun F zeta i * yfun F zeta⁻¹ i = 1 := by
  funext x
  by_cases hx : x i = true <;> simp [yfun, hx, mul_inv_cancel₀ hz0]

lemma prod_yfun_univ (zeta : F) :
    ∏ i : Fin n, yfun F zeta i = fun x => zeta ^ wt x := by
  funext x
  rw [Finset.prod_apply]
  simp only [yfun, wt]
  rw [Finset.prod_ite]
  simp

lemma prod_yfun_mem_Deg (zeta : F) (T : Finset (Fin n)) :
    ∏ i ∈ T, yfun F zeta i ∈ Deg F n T.card := by
  simpa using Deg_prod T (yfun F zeta) 1 (fun j _ => yfun_mem_Deg zeta j)

lemma prod_yfun_sub_one (zeta : F) (T : Finset (Fin n)) :
    ∏ i ∈ T, (yfun F zeta i + (-1)) = (zeta - 1) ^ T.card • mono F T := by
  funext x
  rw [Finset.prod_apply]
  by_cases h : ∀ i ∈ T, x i = true
  · have : ∀ i ∈ T, (yfun F zeta i + (-1)) x = zeta - 1 := by
      intro i hi
      simp [yfun, h i hi]
      ring
    rw [Finset.prod_congr rfl this, Finset.prod_const]
    have hm : mono F T x = 1 := by simp only [mono]; exact if_pos h
    simp [hm]
  · obtain ⟨i, hi, hxi⟩ : ∃ i ∈ T, ¬ (x i = true) := by
      by_contra hc
      exact h (by simpa using hc)
    rw [Finset.prod_eq_zero hi (by simp [yfun, hxi])]
    have hm : mono F T x = 0 := by simp only [mono]; exact if_neg h
    simp [hm]

/-- **Smolensky's counting lemma.** If some function of degree at most `D` agrees on `S`
with `x ↦ ζ ^ (weight x)`, where `ζ ≠ 0, 1`, then `S` has at most
`#{T ⊆ [n] : |T| ≤ n/2 + D}` elements. -/
theorem smolensky_card_bound {D : ℕ} (zeta : F) (hz0 : zeta ≠ 0) (hz1 : zeta ≠ 1)
    (S : Finset (Fin n → Bool)) (G : (Fin n → Bool) → F) (hG : G ∈ Deg F n D)
    (hGS : ∀ x ∈ S, G x = zeta ^ wt x) :
    S.card ≤ Fintype.card {T : Finset (Fin n) // T.card ≤ n / 2 + D} := by
  classical
  set M := n / 2 + D with hM
  -- the restriction map to `S`
  set R : ((Fin n → Bool) → F) →ₗ[F] (↥S → F) :=
    LinearMap.funLeft F F (fun s : ↥S => (s : Fin n → Bool)) with hR
  set W : Submodule F (↥S → F) := Submodule.map R (Deg F n M) with hW
  -- every product of `y`'s restricts into `W`
  have hyprod : ∀ T : Finset (Fin n), R (∏ i ∈ T, yfun F zeta i) ∈ W := by
    intro T
    by_cases hT : T.card ≤ n / 2
    · exact Submodule.mem_map_of_mem
        (Deg_mono (le_trans hT (Nat.le_add_right _ _)) (prod_yfun_mem_Deg zeta T))
    · push_neg at hT
      have hcompl : Tᶜ.card ≤ n / 2 := by
        have h1 : T.card + Tᶜ.card = n := by
          simp
        omega
      -- `∏_{i ∈ T} y i` agrees on `S` with `G * ∏_{i ∈ Tᶜ} y⁻¹`
      have hkey0 : (fun x => zeta ^ wt x) * ∏ i ∈ Tᶜ, yfun F zeta⁻¹ i
          = ∏ i ∈ T, yfun F zeta i := by
        rw [← prod_yfun_univ (F := F) zeta, ← Finset.prod_mul_prod_compl T (yfun F zeta),
          mul_assoc, ← Finset.prod_mul_distrib,
          Finset.prod_congr rfl (fun i (_ : i ∈ Tᶜ) => yfun_mul_inv zeta hz0 i),
          Finset.prod_const_one, mul_one]
      have key : R (∏ i ∈ T, yfun F zeta i) = R (G * ∏ i ∈ Tᶜ, yfun F zeta⁻¹ i) := by
        funext s
        obtain ⟨x, hx⟩ := s
        show (∏ i ∈ T, yfun F zeta i) x = (G * ∏ i ∈ Tᶜ, yfun F zeta⁻¹ i) x
        have hx2 := congrFun hkey0 x
        simp only [Pi.mul_apply] at hx2 ⊢
        rw [hGS x hx, hx2]
      rw [key]
      have hpc : (∏ i ∈ Tᶜ, yfun F zeta⁻¹ i) ∈ Deg F n Tᶜ.card := prod_yfun_mem_Deg zeta⁻¹ Tᶜ
      exact Submodule.mem_map_of_mem (Deg_mono (by omega) (Deg_mul hG hpc))
  -- hence every monomial restricts into `W`
  have hmono : ∀ T : Finset (Fin n), R (mono F T) ∈ W := by
    intro T
    have hzz : (zeta - 1) ≠ 0 := sub_ne_zero_of_ne hz1
    have hpow : ((zeta - 1) ^ T.card) ≠ 0 := pow_ne_zero _ hzz
    have hexp := Finset.prod_add (yfun F zeta) (fun _ => (-1 : (Fin n → Bool) → F)) T
    rw [prod_yfun_sub_one] at hexp
    have happ : ((zeta - 1) ^ T.card) • R (mono F T) ∈ W := by
      rw [← LinearMap.map_smul, hexp, map_sum]
      refine Submodule.sum_mem _ (fun T' hT' => ?_)
      have : (∏ i ∈ T', yfun F zeta i) * ∏ _i ∈ T \ T', (-1 : (Fin n → Bool) → F)
          = ((-1 : F) ^ (T \ T').card) • ∏ i ∈ T', yfun F zeta i := by
        rw [Finset.prod_const]
        funext x
        simp [Pi.smul_apply, mul_comm]
      rw [this, LinearMap.map_smul]
      exact Submodule.smul_mem _ _ (hyprod T')
    have := Submodule.smul_mem W ((zeta - 1) ^ T.card)⁻¹ happ
    rwa [inv_smul_smul₀ hpow] at this
  -- so `W` is everything
  have hWtop : W = ⊤ := by
    have hRsurj : Function.Surjective R := by
      intro g
      refine ⟨fun x => if h : x ∈ S then g ⟨x, h⟩ else 0, ?_⟩
      funext s
      obtain ⟨x, hx⟩ := s
      show (fun x => if h : x ∈ S then g ⟨x, h⟩ else 0) x = _
      simp [hx]
    have htop : (⊤ : Submodule F (↥S → F)) = Submodule.map R (Deg F n n) := by
      rw [Deg_top]
      rw [Submodule.map_top, LinearMap.range_eq_top.2 hRsurj]
    refine le_antisymm le_top ?_
    rw [htop, Deg, Submodule.map_span, Submodule.span_le]
    rintro f ⟨g, ⟨T, rfl⟩, rfl⟩
    exact hmono T.1
  -- and the dimension count finishes the proof
  have h1 : S.card = finrank F (↥S → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : finrank F (↥S → F) = finrank F W := by
    rw [hWtop]
    exact (finrank_top F _).symm
  have h3 : finrank F W ≤ finrank F (Deg F n M) := Submodule.finrank_map_le R (Deg F n M)
  have h4 : finrank F (Deg F n M) ≤ Fintype.card {T : Finset (Fin n) // T.card ≤ M} :=
    finrank_Deg_le M
  omega

end CS

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

