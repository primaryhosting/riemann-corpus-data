import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

variable {A : Type*}

/-- The list of the first `n` moves of the play `f`. -/
def takeF (f : ℕ → A) (n : ℕ) : List A := (List.range n).map f

@[simp] lemma takeF_length (f : ℕ → A) (n : ℕ) : (takeF f n).length = n := by
  simp [takeF]

@[simp] lemma takeF_zero (f : ℕ → A) : takeF f 0 = [] := by simp [takeF]

lemma takeF_succ (f : ℕ → A) (n : ℕ) : takeF f (n + 1) = takeF f n ++ [f n] := by
  simp [takeF, List.range_succ]

lemma takeF_getElem (f : ℕ → A) {n i : ℕ} (h : i < n) :
    (takeF f n)[i]'(by simpa using h) = f i := by
  simp [takeF]

lemma takeF_getD [Inhabited A] (f : ℕ → A) {n i : ℕ} (h : i < n) :
    (takeF f n).getD i default = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), takeF_getElem f h]

lemma takeF_prefix (f : ℕ → A) {m n : ℕ} (h : m ≤ n) : takeF f m <+: takeF f n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ n hn ih => exact ih.trans (by rw [takeF_succ]; exact List.prefix_append _ _)

lemma eq_of_takeF_eq {f g : ℕ → A} {n : ℕ} (h : takeF f n = takeF g n) :
    ∀ i < n, f i = g i := by
  intro i hi
  have := congrArg (fun l => l[i]?) h
  simpa [takeF, List.getElem?_map, List.getElem?_range, hi] using this

/-- A strategy assigns a move to every position (finite sequence of moves played so far). -/
abbrev Strategy (A : Type*) := List A → A

/-- The play `f` follows strategy `σ` for player I (who moves at the even-numbered turns). -/
def FollowsI (f : ℕ → A) (σ : Strategy A) : Prop := ∀ n, Even n → f n = σ (takeF f n)

/-- The play `f` follows strategy `τ` for player II (who moves at the odd-numbered turns). -/
def FollowsII (f : ℕ → A) (τ : Strategy A) : Prop := ∀ n, Odd n → f n = τ (takeF f n)

/-- Player I has a winning strategy in the subgame of `W` starting from the position `p`
(where it is player I's turn, i.e. `p` has even length). -/
def IWinsFrom (W : Set (ℕ → A)) (p : List A) : Prop :=
  ∃ σ : Strategy A, ∀ f : ℕ → A, takeF f p.length = p →
    (∀ n, p.length ≤ n → Even n → f n = σ (takeF f n)) → f ∈ W

/-- Openness in the product topology: every play in `W` has a finite initial segment
all of whose extensions lie in `W`. -/
lemma exists_basic_nbhd [TopologicalSpace A] {W : Set (ℕ → A)} (hW : IsOpen W)
    {f : ℕ → A} (hf : f ∈ W) : ∃ n, ∀ g : ℕ → A, (∀ i < n, g i = f i) → g ∈ W := by
  rw [isOpen_pi_iff] at hW
  obtain ⟨I, u, hu, hsub⟩ := hW f hf
  refine ⟨(I.sup id) + 1, fun g hg => hsub ?_⟩
  intro i hi
  have h1 : i ≤ I.sup id := by simpa using Finset.le_sup (f := id) hi
  rw [hg i (by omega)]
  exact (hu i hi).2

/-- If player I wins the subgame after every reply `b` to the move `a`, then I wins from `p`. -/
lemma IWinsFrom_of_forall [Inhabited A] {W : Set (ℕ → A)} {p : List A}
    (hp : Even p.length) (a : A) (h : ∀ b, IWinsFrom W (p ++ [a, b])) : IWinsFrom W p := by
  classical
  choose S hS using h
  refine ⟨fun q => if (p ++ [a]) <+: q then S (q.getD (p.length + 1) default) q else a, ?_⟩
  intro f hfp hfσ
  have hnp : ¬ (p ++ [a] <+: p) := by
    intro hc
    have := hc.length_le
    simp at this
  have hfa : f p.length = a := by
    have h0 := hfσ p.length le_rfl hp
    rw [hfp] at h0
    simpa [hnp] using h0
  obtain ⟨b, hb⟩ : ∃ b, f (p.length + 1) = b := ⟨_, rfl⟩
  have hq : takeF f (p.length + 2) = p ++ [a, b] := by
    rw [show p.length + 2 = (p.length + 1) + 1 from rfl, takeF_succ, takeF_succ, hfp, hfa, hb]
    simp
  refine hS b f (by rw [show (p ++ [a, b]).length = p.length + 2 by simp]; exact hq) ?_
  intro n hn hev
  have hn2 : p.length + 2 ≤ n := by simpa using hn
  have h1 := hfσ n (by omega) hev
  have hpre : p ++ [a] <+: takeF f n := by
    have h2 : takeF f (p.length + 2) <+: takeF f n := takeF_prefix f hn2
    rw [hq] at h2
    exact List.IsPrefix.trans (by simp) h2
  rw [h1]
  simp only [if_pos hpre, takeF_getD f (show p.length + 1 < n by omega), hb]

/-- From a position that is not winning for player I, every move of player I admits
a reply keeping the position not winning for player I. -/
lemma exists_bad_move [Inhabited A] {W : Set (ℕ → A)} {p : List A}
    (hp : Even p.length) (h : ¬ IWinsFrom W p) (a : A) :
    ∃ b, ¬ IWinsFrom W (p ++ [a, b]) := by
  by_contra hc
  push_neg at hc
  exact h (IWinsFrom_of_forall hp a hc)

/-- **Gale–Stewart theorem**: every open game is determined.

The game is played on a (nonempty, discrete) set of moves `A`; players I and II alternately
choose elements of `A`, player I moving at the even-numbered turns, producing a play
`f : ℕ → A`. Player I wins if the play belongs to the payoff set `W`, which is assumed open
in the product topology. The conclusion is that one of the two players has a winning strategy.
(The proof only uses that `W` is open, so it holds for any topology on `A`; the discreteness
assumption is the standard setting in which "open game" is meant.) -/
theorem Gale_Stewart_open {A : Type*} [Inhabited A] [TopologicalSpace A] [DiscreteTopology A]
    (W : Set (ℕ → A)) (hW : IsOpen W) :
    (∃ σ : Strategy A, ∀ f : ℕ → A, FollowsI f σ → f ∈ W) ∨
    (∃ τ : Strategy A, ∀ f : ℕ → A, FollowsII f τ → f ∉ W) := by
  classical
  by_cases hI : IWinsFrom W []
  · obtain ⟨σ, hσ⟩ := hI
    exact Or.inl ⟨σ, fun f hf => hσ f (by simp) (fun n _ hn => hf n hn)⟩
  · refine Or.inr ⟨fun q => if h : ∃ b, ¬ IWinsFrom W (q ++ [b]) then h.choose else default,
      fun f hf hfW => ?_⟩
    have claim : ∀ k, ¬ IWinsFrom W (takeF f (2 * k)) := by
      intro k
      induction k with
      | zero => simpa using hI
      | succ k ih =>
        have hp : Even (takeF f (2 * k)).length := by simp
        obtain ⟨b, hb⟩ := exists_bad_move hp ih (f (2 * k))
        have hq : takeF f (2 * k + 1) = takeF f (2 * k) ++ [f (2 * k)] := takeF_succ f (2 * k)
        have hex : ∃ b, ¬ IWinsFrom W (takeF f (2 * k + 1) ++ [b]) := by
          refine ⟨b, ?_⟩
          rw [hq]
          simpa using hb
        have hval := hf (2 * k + 1) ⟨k, by ring⟩
        have hstep : takeF f (2 * (k + 1)) = takeF f (2 * k + 1) ++ [f (2 * k + 1)] := by
          rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring]; exact takeF_succ f _
        rw [hstep, hval]
        simpa only [dif_pos hex] using hex.choose_spec
    obtain ⟨n, hn⟩ := exists_basic_nbhd hW hfW
    refine claim n ⟨fun _ => default, fun g hg _ => hn g ?_⟩
    rw [takeF_length] at hg
    exact fun i hi => eq_of_takeF_eq hg i (by omega)

/-- The position reached after `n` moves when player I follows `σ` and player II follows `τ`. -/
def playAux (σ τ : Strategy A) : ℕ → List A
  | 0 => []
  | n + 1 => playAux σ τ n ++
      [if Even (playAux σ τ n).length then σ (playAux σ τ n) else τ (playAux σ τ n)]

lemma playAux_length (σ τ : Strategy A) (n : ℕ) : (playAux σ τ n).length = n := by
  induction n with
  | zero => simp [playAux]
  | succ n ih => simp [playAux, ih]

/-- Any pair of strategies determines a play following both of them; in particular the two
disjuncts of the determinacy statement are not vacuous. -/
lemma exists_play (σ τ : Strategy A) : ∃ f : ℕ → A, FollowsI f σ ∧ FollowsII f τ := by
  classical
  refine ⟨fun n => if Even n then σ (playAux σ τ n) else τ (playAux σ τ n), ?_, ?_⟩ <;>
  · have key : ∀ n, takeF (fun n => if Even n then σ (playAux σ τ n) else τ (playAux σ τ n)) n
        = playAux σ τ n := by
      intro n
      induction n with
      | zero => simp [playAux]
      | succ n ih => rw [takeF_succ, ih]; simp [playAux, playAux_length]
    intro n hn
    rw [key n]
    simp [Nat.not_even_iff_odd, hn]

/-- The two alternatives in `Gale_Stewart_open` are mutually exclusive: the two players cannot
both have a winning strategy. -/
theorem not_both_win (W : Set (ℕ → A)) :
    ¬ ((∃ σ : Strategy A, ∀ f : ℕ → A, FollowsI f σ → f ∈ W) ∧
       (∃ τ : Strategy A, ∀ f : ℕ → A, FollowsII f τ → f ∉ W)) := by
  rintro ⟨⟨σ, hσ⟩, τ, hτ⟩
  obtain ⟨f, hf1, hf2⟩ := exists_play σ τ
  exact hτ f hf2 (hσ f hf1)

end Frontier

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

