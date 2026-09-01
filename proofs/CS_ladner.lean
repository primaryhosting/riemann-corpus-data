/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: the required header comment
above is a module docstring, and Lean only accepts a module docstring at the
very beginning of a file when the file has no `import` commands.  Everything
below therefore uses only the Lean 4 core library.
-/

namespace CS

open Classical

/-- A language: a set of (encoded) strings, i.e. a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/-! ## Classical helpers -/

theorem not_forall_exists {α : Sort _} {p : α → Prop} (h : ¬ ∀ a, p a) : ∃ a, ¬ p a :=
  Classical.byContradiction fun hh =>
    h fun a => Classical.byContradiction fun hp => hh ⟨a, hp⟩

/-- A `Nat`-valued function bounded by `N` attains a maximum value. -/
theorem exists_max : ∀ (N : Nat) (g : Nat → Nat), (∀ n, g n ≤ N) → ∃ n0, ∀ n, g n ≤ g n0 := by
  intro N
  induction N with
  | zero =>
      intro g h
      exact ⟨0, fun n => by have h1 := h n; have h2 := h 0; omega⟩
  | succ N ih =>
      intro g h
      by_cases hc : ∀ n, g n ≤ N
      · exact ih g hc
      · obtain ⟨m, hm⟩ := not_forall_exists hc
        refine ⟨m, fun n => ?_⟩
        have h1 := h n
        omega

/-! ## Ladner's construction

Fix an enumeration `dec` of the polynomial-time deciders, an enumeration `red`
of the polynomial-time computable functions, a language `K`, and a *clock*
`clock : Nat → Nat` (in the intended instantiation, `clock n` is roughly
`log n`; the two requirements on it are that `clock n ≤ n`, which keeps the
construction well-founded and makes it polynomial-time computable, and that it
is nondecreasing and unbounded).

The gap function `gapF` is built stage by stage: at input `n` the current stage
is `gapF n`.  An even stage `2 * i` is devoted to diagonalising against the
`i`-th polynomial-time decider, and an odd stage `2 * i + 1` to killing the
`i`-th candidate reduction of `K` to the constructed language; the stage
advances as soon as a witness of failure is spotted inside the clock bound. -/

section Construction

variable (dec : Nat → Nat → Bool) (red : Nat → Nat → Nat) (K : Lang) (clock : Nat → Nat)

/-- The "defeat" condition of Ladner's blow-hole construction, evaluated at
input `n` for the stage `g n`.  All queries made by the condition are at
arguments `≤ clock n ≤ n`, so it only depends on the values of `g` on
`[0, n]`. -/
def defeated (g : Nat → Nat) (n : Nat) : Prop :=
  (g n % 2 = 0 ∧ ∃ z, z ≤ clock n ∧ ¬ (dec (g n / 2) z = true ↔ (K z ∧ g z % 2 = 0))) ∨
  (g n % 2 = 1 ∧ ∃ z, z ≤ clock n ∧ red (g n / 2) z ≤ clock n ∧
      ¬ (K z ↔ (K (red (g n / 2) z) ∧ g (red (g n / 2) z) % 2 = 0)))

/-- Stage-by-stage approximation of the gap function: `fAux m` agrees with the
gap function on all inputs `≤ m`. -/
noncomputable def fAux : Nat → Nat → Nat
  | 0 => fun _ => 0
  | (n + 1) => fun m =>
      if m ≤ n then fAux n m
      else fAux n n + (if defeated dec red K clock (fAux n) n then 1 else 0)

/-- The gap function of Ladner's construction. -/
noncomputable def gapF (n : Nat) : Nat := fAux dec red K clock n n

/-- The language obtained from `K` by "blowing holes" along the gap function:
`x` is kept exactly when the gap function is even at `x`. -/
noncomputable def ladnerLang : Lang := fun x => K x ∧ gapF dec red K clock x % 2 = 0

theorem fAux_stable :
    ∀ (m k : Nat), k ≤ m → fAux dec red K clock m k = gapF dec red K clock k := by
  intro m
  induction m with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst this
      rfl
  | succ n ih =>
      intro k hk
      by_cases hkn : k ≤ n
      · simp only [fAux]
        rw [if_pos hkn]
        exact ih k hkn
      · have : k = n + 1 := by omega
        subst this
        rfl

theorem defeated_congr {g h : Nat → Nat} {n : Nat} (hcl : clock n ≤ n)
    (H : ∀ k, k ≤ n → g k = h k) :
    defeated dec red K clock g n ↔ defeated dec red K clock h n := by
  have hn : g n = h n := H n (Nat.le_refl n)
  unfold defeated
  rw [hn]
  constructor
  · rintro (⟨he, z, hz, hw⟩ | ⟨he, z, hz, hred, hw⟩)
    · exact Or.inl ⟨he, z, hz, by rw [H z (Nat.le_trans hz hcl)] at hw; exact hw⟩
    · exact Or.inr ⟨he, z, hz, hred, by rw [H _ (Nat.le_trans hred hcl)] at hw; exact hw⟩
  · rintro (⟨he, z, hz, hw⟩ | ⟨he, z, hz, hred, hw⟩)
    · exact Or.inl ⟨he, z, hz, by rw [H z (Nat.le_trans hz hcl)]; exact hw⟩
    · exact Or.inr ⟨he, z, hz, hred, by rw [H _ (Nat.le_trans hred hcl)]; exact hw⟩

theorem gapF_zero : gapF dec red K clock 0 = 0 := rfl

theorem gapF_succ (hcl : ∀ n, clock n ≤ n) (n : Nat) :
    gapF dec red K clock (n + 1) =
      gapF dec red K clock n +
        (if defeated dec red K clock (gapF dec red K clock) n then 1 else 0) := by
  have h1 : gapF dec red K clock (n + 1) = fAux dec red K clock (n + 1) (n + 1) := rfl
  rw [h1]
  simp only [fAux]
  rw [if_neg (by omega : ¬ (n + 1 ≤ n))]
  have h2 : ∀ k, k ≤ n → fAux dec red K clock n k = gapF dec red K clock k :=
    fAux_stable dec red K clock n
  rw [h2 n (Nat.le_refl n), defeated_congr dec red K clock (hcl n) h2]

theorem gapF_le_succ (hcl : ∀ n, clock n ≤ n) (n : Nat) :
    gapF dec red K clock n ≤ gapF dec red K clock (n + 1) := by
  rw [gapF_succ dec red K clock hcl]
  omega

theorem gapF_succ_le (hcl : ∀ n, clock n ≤ n) (n : Nat) :
    gapF dec red K clock (n + 1) ≤ gapF dec red K clock n + 1 := by
  rw [gapF_succ dec red K clock hcl]
  split <;> omega

theorem gapF_mono (hcl : ∀ n, clock n ≤ n) :
    ∀ (m n : Nat), m ≤ n → gapF dec red K clock m ≤ gapF dec red K clock n := by
  intro m n
  induction n with
  | zero =>
      intro h
      have : m = 0 := by omega
      subst this
      exact Nat.le_refl _
  | succ k ih =>
      intro h
      by_cases hk : m ≤ k
      · have h1 := ih hk
        have h2 := gapF_le_succ dec red K clock hcl k
        omega
      · have : m = k + 1 := by omega
        subst this
        exact Nat.le_refl _

/-- If the gap function ever exceeds `v`, then it passes through the value `v`,
and at the input where it leaves the value `v` the defeat condition holds. -/
theorem exists_defeat (hcl : ∀ n, clock n ≤ n) :
    ∀ (m v : Nat), v + 1 ≤ gapF dec red K clock m →
      ∃ n, gapF dec red K clock n = v ∧ defeated dec red K clock (gapF dec red K clock) n := by
  intro m
  induction m with
  | zero =>
      intro v h
      rw [gapF_zero] at h
      omega
  | succ k ih =>
      intro v h
      by_cases hk : v + 1 ≤ gapF dec red K clock k
      · exact ih v hk
      · have hstep := gapF_succ_le dec red K clock hcl k
        have heq1 : gapF dec red K clock (k + 1) = v + 1 := by omega
        have heq0 : gapF dec red K clock k = v := by omega
        refine ⟨k, heq0, ?_⟩
        by_cases hd : defeated dec red K clock (gapF dec red K clock) k
        · exact hd
        · rw [gapF_succ dec red K clock hcl, if_neg hd] at heq1
          omega

end Construction

/-- **Ladner's theorem: if `P ≠ NP` then `NP`-intermediate languages exist.**

The statement is formulated over an abstract but faithful axiomatisation of the
relevant structure of complexity theory.  Languages are predicates on `Nat`
(strings encoded as naturals) and:

* `P` and `NP` are classes of languages with `P ⊆ NP` (`hPsubNP`);
* `dec` enumerates the polynomial-time deciders, so that `P` consists exactly
  of the languages decided by some `dec i` (`hPdec`: a recursive presentation
  of `P`);
* `red` enumerates the polynomial-time computable functions, so that `Red A B`
  (polynomial-time many-one reducibility) holds exactly when some `red i` is a
  reduction of `A` to `B` (`hRedEnum`);
* `P` contains the empty language (`hPempty`), is closed under variation on a
  bounded set of inputs (`hPfinvar`), and is closed downwards under `Red`
  (`hPdown`);
* `K` is an `NP`-complete language (`hKNP`, `hKhard`; e.g. SAT, by Cook–Levin);
* `clock` is the clock of the construction, nondecreasing, unbounded and
  bounded above by the identity (in the intended instantiation, `clock n` is
  the logarithm of `n`);
* `hGapNP` is the polynomial-time-computability input of Ladner's proof: the
  clocked gap function is polynomial-time computable, hence the language
  obtained from `K` by blowing holes along it is again in `NP`.

The conclusion is the existence of an `NP`-intermediate language: a language
`A` in `NP` which is not in `P` and which is not `NP`-hard (hence not
`NP`-complete).

The proof is Ladner's "blowing holes" diagonalisation.  The gap function is
built so that it advances to the next stage as soon as the current adversary (a
decider at an even stage, a reduction at an odd stage) has been defeated within
the clock bound.  A case split on whether the gap function is bounded then
yields the result: if it stabilises at an even stage the constructed language
is in `P` and is a bounded variant of `K`, forcing `K ∈ P`; if it stabilises at
an odd stage the constructed language is bounded, hence in `P`, while `K`
reduces to it, again forcing `K ∈ P`; and if it is unbounded every decider and
every reduction is explicitly defeated. -/
theorem ladner
    (P NP : Lang → Prop) (Red : Lang → Lang → Prop)
    (dec : Nat → Nat → Bool) (red : Nat → Nat → Nat) (K : Lang) (clock : Nat → Nat)
    (hPdec : ∀ A : Lang, P A ↔ ∃ i, ∀ x, (A x ↔ dec i x = true))
    (hRedEnum : ∀ A B : Lang, Red A B ↔ ∃ i, ∀ x, (A x ↔ B (red i x)))
    (hPsubNP : ∀ A : Lang, P A → NP A)
    (hPempty : P (fun _ => False))
    (hPfinvar : ∀ A B : Lang, (∃ N, ∀ x, N ≤ x → (A x ↔ B x)) → P A → P B)
    (hPdown : ∀ A B : Lang, Red A B → P B → P A)
    (hKNP : NP K) (hKhard : ∀ B : Lang, NP B → Red B K)
    (hclock_le : ∀ n, clock n ≤ n)
    (hclock_mono : ∀ a b, a ≤ b → clock a ≤ clock b)
    (hclock_unb : ∀ M, ∃ n, M ≤ clock n)
    (hGapNP : NP (ladnerLang dec red K clock))
    (hPNP : P ≠ NP) :
    ∃ A : Lang, NP A ∧ ¬ P A ∧ ¬ (∀ B : Lang, NP B → Red B A) := by
  classical
  -- `K` is not in `P`, since it is `NP`-complete and `P ≠ NP`.
  have hKP : ¬ P K := by
    intro hK
    exact hPNP (funext fun A => propext
      ⟨fun h => hPsubNP A h, fun h => hPdown A K (hKhard A h) hK⟩)
  -- The clock eventually exceeds any bound, at arbitrarily late inputs.
  have hbig : ∀ (M n0 : Nat), ∃ n, n0 ≤ n ∧ M ≤ clock n := by
    intro M n0
    obtain ⟨m, hm⟩ := hclock_unb M
    refine ⟨max m n0, Nat.le_max_right _ _, ?_⟩
    exact Nat.le_trans hm (hclock_mono m (max m n0) (Nat.le_max_left _ _))
  -- The gap function is unbounded.
  have hunb : ∀ N : Nat, ∃ n, N < gapF dec red K clock n := by
    intro N
    by_cases hex : ∃ n, N < gapF dec red K clock n
    · exact hex
    · exfalso
      have hN : ∀ n, gapF dec red K clock n ≤ N := by
        intro n
        by_cases hle : gapF dec red K clock n ≤ N
        · exact hle
        · exact absurd ⟨n, by omega⟩ hex
      -- bounded and monotone, hence eventually constant
      obtain ⟨n0, hn0⟩ := exists_max N (gapF dec red K clock) hN
      have hconst : ∀ n, n0 ≤ n → gapF dec red K clock n = gapF dec red K clock n0 := by
        intro n hn
        have h1 := hn0 n
        have h2 := gapF_mono dec red K clock hclock_le n0 n hn
        omega
      -- from `n0` on, the defeat condition never holds
      have hnodef : ∀ n, n0 ≤ n → ¬ defeated dec red K clock (gapF dec red K clock) n := by
        intro n hn hd
        have h1 := gapF_succ dec red K clock hclock_le n
        rw [if_pos hd, hconst n hn, hconst (n + 1) (by omega)] at h1
        omega
      by_cases hev : gapF dec red K clock n0 % 2 = 0
      · -- Even final stage: the constructed language is decided by machine
        -- `s / 2`, hence lies in `P`; but it agrees with `K` beyond `n0`, so
        -- `K ∈ P`, a contradiction.
        have hdecA : ∀ z, (dec (gapF dec red K clock n0 / 2) z = true ↔
            (K z ∧ gapF dec red K clock z % 2 = 0)) := by
          intro z
          by_cases hw : (dec (gapF dec red K clock n0 / 2) z = true ↔
              (K z ∧ gapF dec red K clock z % 2 = 0))
          · exact hw
          · exfalso
            obtain ⟨n, hn, hz⟩ := hbig z n0
            refine hnodef n hn (Or.inl ⟨?_, z, hz, ?_⟩)
            · rw [hconst _ hn]; exact hev
            · rw [hconst _ hn]; exact hw
        have hAP : P (ladnerLang dec red K clock) := by
          rw [hPdec]
          exact ⟨gapF dec red K clock n0 / 2, fun x => (hdecA x).symm⟩
        refine hKP (hPfinvar (ladnerLang dec red K clock) K ⟨n0, ?_⟩ hAP)
        intro x hx
        have hgx : gapF dec red K clock x % 2 = 0 := by rw [hconst x hx]; exact hev
        exact ⟨fun h => h.1, fun h => ⟨h, hgx⟩⟩
      · -- Odd final stage: `K` reduces to the constructed language, which is
        -- empty beyond `n0`, hence in `P`; so `K ∈ P`, a contradiction.
        have hodd : gapF dec red K clock n0 % 2 = 1 := by omega
        have hredA : ∀ z, (K z ↔
            ladnerLang dec red K clock (red (gapF dec red K clock n0 / 2) z)) := by
          intro z
          by_cases hw : (K z ↔
              ladnerLang dec red K clock (red (gapF dec red K clock n0 / 2) z))
          · exact hw
          · exfalso
            obtain ⟨n, hn, hz⟩ :=
              hbig (max z (red (gapF dec red K clock n0 / 2) z)) n0
            refine hnodef n hn (Or.inr ⟨?_, z, ?_, ?_, ?_⟩)
            · rw [hconst _ hn]; exact hodd
            · exact Nat.le_trans (Nat.le_max_left _ _) hz
            · rw [hconst _ hn]
              exact Nat.le_trans (Nat.le_max_right _ _) hz
            · rw [hconst _ hn]
              exact hw
        have hRedKA : Red K (ladnerLang dec red K clock) :=
          (hRedEnum K (ladnerLang dec red K clock)).mpr
            ⟨gapF dec red K clock n0 / 2, hredA⟩
        have hAP : P (ladnerLang dec red K clock) := by
          refine hPfinvar (fun _ => False) (ladnerLang dec red K clock) ⟨n0, ?_⟩ hPempty
          intro x hx
          have hgx : gapF dec red K clock x % 2 = 1 := by rw [hconst x hx]; exact hodd
          exact ⟨fun h => absurd h (fun h => h), fun h => by
            have h2 := h.2
            omega⟩
        exact hKP (hPdown K (ladnerLang dec red K clock) hRedKA hAP)
  refine ⟨ladnerLang dec red K clock, hGapNP, ?_, ?_⟩
  · -- The constructed language is not in `P`: every decider is defeated at
    -- some even stage.
    intro hAP
    obtain ⟨i, hi⟩ := (hPdec (ladnerLang dec red K clock)).mp hAP
    obtain ⟨m, hm⟩ := hunb (2 * i)
    obtain ⟨n, hn, hd⟩ := exists_defeat dec red K clock hclock_le m (2 * i) (by omega)
    rcases hd with ⟨_, z, _, hw⟩ | ⟨hpar, _⟩
    · rw [hn] at hw
      have h3 : (2 * i) / 2 = i := by omega
      rw [h3] at hw
      exact hw (hi z).symm
    · rw [hn] at hpar
      omega
  · -- The constructed language is not `NP`-hard: every candidate reduction of
    -- `K` to it is defeated at some odd stage.
    intro hhard
    obtain ⟨i, hi⟩ := (hRedEnum K (ladnerLang dec red K clock)).mp (hhard K hKNP)
    obtain ⟨m, hm⟩ := hunb (2 * i + 1)
    obtain ⟨n, hn, hd⟩ := exists_defeat dec red K clock hclock_le m (2 * i + 1) (by omega)
    rcases hd with ⟨hpar, _⟩ | ⟨_, z, _, _, hw⟩
    · rw [hn] at hpar
      omega
    · rw [hn] at hw
      have h3 : (2 * i + 1) / 2 = i := by omega
      rw [h3] at hw
      exact hw (hi z)

end CS

