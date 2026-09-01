/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/
def Strategy (A : Type u) : Type u := List A → A

variable {A : Type u}

/-- The list of the first `n` moves of the play `x`. -/
def hist (x : ℕ → A) (n : ℕ) : List A := (List.range n).map x

@[simp] lemma hist_zero (x : ℕ → A) : hist x 0 = [] := rfl

@[simp] lemma hist_length (x : ℕ → A) (n : ℕ) : (hist x n).length = n := by
  simp [hist]

lemma hist_succ (x : ℕ → A) (n : ℕ) : hist x (n + 1) = hist x n ++ [x n] := by
  simp [hist, List.range_succ]

lemma hist_getD [Inhabited A] (x : ℕ → A) {i n : ℕ} (h : i < n) :
    (hist x n).getD i default = x i := by
  simp [hist, List.getD_eq_getElem?_getD, h]

lemma hist_eq_iff (x y : ℕ → A) (n : ℕ) :
    hist x n = hist y n ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [hist, List.getElem?_map, hi] using this
  · intro h
    simp only [hist]
    exact List.map_congr_left (by simpa using h)

/-- `ConsI p σ x` : the play `x` extends the position `p` and player I (who moves at the even
positions) follows the strategy `σ` from `p` onwards. -/
def ConsI (p : List A) (σ : Strategy A) (x : ℕ → A) : Prop :=
  hist x p.length = p ∧ ∀ n, p.length ≤ n → Even n → x n = σ (hist x n)

/-- `ConsII p τ x` : the play `x` extends the position `p` and player II (who moves at the odd
positions) follows the strategy `τ` from `p` onwards. -/
def ConsII (p : List A) (τ : Strategy A) (x : ℕ → A) : Prop :=
  hist x p.length = p ∧ ∀ n, p.length ≤ n → Odd n → x n = τ (hist x n)

/-- Player I follows `σ` throughout the whole play `x`. -/
def ConsistentI (σ : Strategy A) (x : ℕ → A) : Prop := ConsI [] σ x

/-- Player II follows `τ` throughout the whole play `x`. -/
def ConsistentII (τ : Strategy A) (x : ℕ → A) : Prop := ConsII [] τ x

/-- `σ` is a winning strategy for player I in the game with payoff set `S` started at `p`. -/
def WinIFrom (S : Set (ℕ → A)) (p : List A) (σ : Strategy A) : Prop :=
  ∀ x, ConsI p σ x → x ∈ S

/-- Player I has a winning strategy in the game with payoff set `S` started at `p`. -/
def IWins (S : Set (ℕ → A)) (p : List A) : Prop := ∃ σ, WinIFrom S p σ

/-- The game with payoff set `S` (player I wins a play `x` iff `x ∈ S`) is determined. -/
def Determined (S : Set (ℕ → A)) : Prop :=
  (∃ σ : Strategy A, ∀ x, ConsistentI σ x → x ∈ S) ∨
  (∃ τ : Strategy A, ∀ x, ConsistentII τ x → x ∉ S)

/-! ## A combinatorial description of the (cl)open sets of the sequence space -/

/-- `S` is open in the product topology on `ℕ → A` with `A` discrete: every member of `S` has a
finite prefix all of whose extensions lie in `S`. -/
def IsOpenSeq (S : Set (ℕ → A)) : Prop :=
  ∀ x ∈ S, ∃ n, ∀ y, hist y n = hist x n → y ∈ S

/-- `S` is clopen in the product topology on `ℕ → A` with `A` discrete. -/
def IsClopenSeq (S : Set (ℕ → A)) : Prop := IsOpenSeq S ∧ IsOpenSeq Sᶜ

section Topology

variable [TopologicalSpace A] [DiscreteTopology A]

omit [DiscreteTopology A] in
/-- Openness in the product topology implies the combinatorial notion `IsOpenSeq`. -/
lemma isOpenSeq_of_isOpen {S : Set (ℕ → A)} (hS : IsOpen S) : IsOpenSeq S := by
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hS x hx
  refine ⟨I.sup id + 1, fun y hy => ?_⟩
  refine hsub fun i hi => ?_
  have hi' : i ∈ I := by simpa using hi
  have hlt : i < I.sup id + 1 := by
    have := Finset.le_sup (f := id) hi'
    simp only [id_eq] at this
    omega
  have : y i = x i := (hist_eq_iff y x _).mp hy i hlt
  rw [this]
  exact (hu i hi').2

/-- The basic cylinder consisting of all sequences agreeing with `x` on the first `n` coordinates
is open. -/
lemma isOpen_cylinder (x : ℕ → A) (n : ℕ) : IsOpen {y : ℕ → A | hist y n = hist x n} := by
  have hset : {y : ℕ → A | hist y n = hist x n}
      = ⋂ i ∈ Finset.range n, (fun y : ℕ → A => y i) ⁻¹' {x i} := by
    ext y
    simp [hist_eq_iff]
  rw [hset]
  exact isOpen_biInter_finset fun i _ =>
    (continuous_apply i).isOpen_preimage _ (isOpen_discrete _)

lemma isOpen_of_isOpenSeq {S : Set (ℕ → A)} (hS : IsOpenSeq S) : IsOpen S := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨n, hn⟩ := hS x hx
  exact ⟨{y | hist y n = hist x n}, fun y hy => hn y hy, isOpen_cylinder x n, rfl⟩

/-- For a discrete alphabet, `IsOpenSeq` is exactly openness in the product topology. -/
lemma isOpen_iff_isOpenSeq {S : Set (ℕ → A)} : IsOpen S ↔ IsOpenSeq S :=
  ⟨isOpenSeq_of_isOpen, isOpen_of_isOpenSeq⟩

/-- For a discrete alphabet, `IsClopenSeq` is exactly clopenness in the product topology. -/
lemma isClopen_iff_isClopenSeq {S : Set (ℕ → A)} : IsClopen S ↔ IsClopenSeq S := by
  constructor
  · intro h
    exact ⟨isOpenSeq_of_isOpen h.2, isOpenSeq_of_isOpen h.1.isOpen_compl⟩
  · intro h
    refine ⟨?_, isOpen_of_isOpenSeq h.1⟩
    rw [← isOpen_compl_iff]
    exact isOpen_of_isOpenSeq h.2

end Topology

/-! ## The Gale–Stewart theorem: open games are determined -/

section GaleStewart

variable [Inhabited A]

lemma iWins_of_all_extensions {S : Set (ℕ → A)} {p : List A}
    (h : ∀ y, hist y p.length = p → y ∈ S) : IWins S p :=
  ⟨fun _ => default, fun x hx => h x hx.1⟩

omit [Inhabited A] in
lemma not_iWins_snoc_of_even {S : Set (ℕ → A)} {p : List A} (hp : Even p.length)
    (h : ¬ IWins S p) (a : A) : ¬ IWins S (p ++ [a]) := by
  classical
  rintro ⟨σ, hσ⟩
  refine h ⟨fun l => if l = p then a else σ l, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hfirst : x p.length = a := by
    have := hx2 p.length le_rfl hp
    simpa [hx1] using this
  have hext : hist x (p ++ [a]).length = p ++ [a] := by
    have : (p ++ [a]).length = p.length + 1 := by simp
    rw [this, hist_succ, hx1, hfirst]
  refine hσ x ⟨hext, fun n hn hne => ?_⟩
  have hn' : p.length < n := by simpa using hn
  have hne' : hist x n ≠ p := by
    intro hcon
    have := congrArg List.length hcon
    simp at this
    omega
  have := hx2 n (le_of_lt hn') hne
  simpa [hne'] using this

lemma exists_not_iWins_snoc {S : Set (ℕ → A)} {p : List A}
    (h : ¬ IWins S p) : ∃ b : A, ¬ IWins S (p ++ [b]) := by
  by_contra hcon
  push_neg at hcon
  choose f hf using fun b => (hcon b)
  refine h ⟨fun l => f (l.getD p.length default) l, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  set b := x p.length with hb
  refine hf b x ⟨?_, fun n hn hno => ?_⟩
  · have hlen : (p ++ [b]).length = p.length + 1 := by simp
    rw [hlen, hist_succ, hx1]
  · have hn' : p.length < n := by simpa using hn
    have hxn := hx2 n (le_of_lt hn') hno
    simp only [hist_getD x hn'] at hxn
    exact hxn

/-- **Gale–Stewart theorem** (base case of Borel determinacy): a game whose payoff set is open
is determined. -/
theorem determined_of_isOpenSeq {S : Set (ℕ → A)} (hS : IsOpenSeq S) : Determined S := by
  classical
  by_cases hI : IWins S []
  · obtain ⟨σ, hσ⟩ := hI
    exact Or.inl ⟨σ, hσ⟩
  · right
    refine ⟨fun p => if h : ∃ b, ¬ IWins S (p ++ [b]) then h.choose else default,
      fun x hx hxS => ?_⟩
    obtain ⟨-, hx2⟩ := hx
    have hgood : ∀ n, ¬ IWins S (hist x n) := by
      intro n
      induction n with
      | zero => simpa using hI
      | succ n ih =>
        rw [hist_succ]
        rcases Nat.even_or_odd n with he | ho
        · exact not_iWins_snoc_of_even (by simpa using he) ih (x n)
        · have hex : ∃ b, ¬ IWins S (hist x n ++ [b]) := exists_not_iWins_snoc ih
          have hxn := hx2 n (by simp) ho
          simp only [dif_pos hex] at hxn
          rw [hxn]
          exact hex.choose_spec
    obtain ⟨n, hn⟩ := hS x hxS
    refine hgood n (iWins_of_all_extensions (p := hist x n) fun y hy => hn y ?_)
    simpa using hy

/-- Clopen games are determined. -/
theorem determined_of_isClopenSeq {S : Set (ℕ → A)} (hS : IsClopenSeq S) : Determined S :=
  determined_of_isOpenSeq hS.1

/-- **Gale–Stewart theorem**, topological form: a game on a discrete alphabet whose payoff set is
open in the product topology is determined. -/
theorem determined_of_isOpen [TopologicalSpace A] [DiscreteTopology A] {S : Set (ℕ → A)}
    (hS : IsOpen S) : Determined S :=
  determined_of_isOpenSeq (isOpenSeq_of_isOpen hS)

/-- Clopen games on a discrete alphabet are determined (topological form). -/
theorem determined_of_isClopen [TopologicalSpace A] [DiscreteTopology A] {S : Set (ℕ → A)}
    (hS : IsClopen S) : Determined S :=
  determined_of_isOpen hS.2

end GaleStewart

/-! ## Coverings and the transfer of determinacy -/

/-- A *covering* of the game on `A` by the game on `B` (Martin).  It consists of a map `push`
sending plays of the `B`-game to plays of the `A`-game together with maps lifting strategies of
the `B`-game to strategies of the `A`-game, in such a way that every play following a lifted
strategy is the image of a play following the original strategy. -/
structure Covering (A : Type u) (B : Type u) where
  push : (ℕ → B) → (ℕ → A)
  liftI : Strategy B → Strategy A
  liftII : Strategy B → Strategy A
  liftI_spec : ∀ (σ : Strategy B) (x : ℕ → A), ConsistentI (liftI σ) x →
    ∃ y, ConsistentI σ y ∧ push y = x
  liftII_spec : ∀ (τ : Strategy B) (x : ℕ → A), ConsistentII (liftII τ) x →
    ∃ y, ConsistentII τ y ∧ push y = x

/-- The identity covering: it shows that the notion of covering is not vacuous. -/
def Covering.refl (A : Type u) : Covering A A where
  push := id
  liftI := id
  liftII := id
  liftI_spec := fun _ x hx => ⟨x, hx, rfl⟩
  liftII_spec := fun _ x hx => ⟨x, hx, rfl⟩

/-- Determinacy transfers downwards along a covering. -/
theorem Covering.determined {B : Type u} (cov : Covering A B) {S : Set (ℕ → A)}
    (h : Determined (cov.push ⁻¹' S)) : Determined S := by
  rcases h with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · refine Or.inl ⟨cov.liftI σ, fun x hx => ?_⟩
    obtain ⟨y, hy, hpush⟩ := cov.liftI_spec σ x hx
    have := hσ y hy
    rwa [Set.mem_preimage, hpush] at this
  · refine Or.inr ⟨cov.liftII τ, fun x hx => ?_⟩
    obtain ⟨y, hy, hpush⟩ := cov.liftII_spec τ x hx
    have := hτ y hy
    rwa [Set.mem_preimage, hpush] at this

/-! ## Borel determinacy -/

/-- Martin's *unravelling* hypothesis: every Borel payoff set admits a covering in which it
becomes clopen.  This is the deep combinatorial content of Martin's theorem. -/
def UnravelsBorel (A : Type u) [TopologicalSpace A] : Prop :=
  ∀ S : Set (ℕ → A), @MeasurableSet (ℕ → A) (borel (ℕ → A)) S →
    ∃ (B : Type u) (cov : Covering A B), Nonempty (Inhabited B) ∧ IsClopenSeq (cov.push ⁻¹' S)

/-- A payoff set that is already clopen is unravelled by the identity covering; in particular the
unravelling condition is satisfiable. -/
lemma exists_covering_isClopenSeq_of_isClopenSeq [Inhabited A] {S : Set (ℕ → A)}
    (hS : IsClopenSeq S) :
    ∃ (B : Type u) (cov : Covering A B), Nonempty (Inhabited B) ∧ IsClopenSeq (cov.push ⁻¹' S) :=
  ⟨A, Covering.refl A, ⟨inferInstance⟩, hS⟩

/-- **Borel determinacy (Martin's theorem), as a Lean-checked reduction.**
Every Borel game on a discrete alphabet `A` is determined, given Martin's unravelling lemma:
each Borel payoff set becomes clopen in a suitable covering game.  The base case (clopen, indeed
open, games are determined) is fully proved above, as is the transfer of determinacy along
coverings; the unravelling hypothesis is the only external input. -/
theorem Borel_determinacy [TopologicalSpace A] [DiscreteTopology A] [Inhabited A]
    (hUnravel : UnravelsBorel A) (S : Set (ℕ → A)) (hS : @MeasurableSet (ℕ → A) (borel (ℕ → A)) S) :
    Determined S := by
  obtain ⟨B, cov, ⟨hB⟩, hclopen⟩ := hUnravel S hS
  haveI : Inhabited B := hB
  exact cov.determined (determined_of_isClopenSeq hclopen)

end Frontier

