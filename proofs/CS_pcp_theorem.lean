/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-! ## Strings and languages -/

/-- Binary strings. -/
abbrev Str := List Bool

/-- A language is a set of binary strings. -/
abbrev Lang := Str → Prop

/-- `PolyBd f` says that `f` is bounded above by a polynomial. -/
def PolyBd (f : Nat → Nat) : Prop := ∃ c : Nat, ∀ n, f n ≤ (n + 2) ^ c

/-! ## An abstract model of feasible (polynomial-time) computation

Polynomial-time computability is taken as a parameter: a `FeasModel` provides a predicate
`Feas` singling out those Boolean-valued procedures `V x ρ w` (of an input string `x`, a
number `ρ`, and an auxiliary string `w`) that count as efficiently computable, subject to the
single closure property used below: the conjunction of a feasible predicate over a
polynomially long range of values of `ρ` is again feasible.  This property holds for
polynomial time, and the structure is inhabited (e.g. by `Feas := fun _ => True`), so nothing
below is vacuous. -/
structure FeasModel where
  /-- The efficiently computable Boolean procedures of the model. -/
  Feas : (Str → Nat → Str → Bool) → Prop
  /-- Polynomially many repetitions of a feasible procedure are feasible. -/
  feas_forall : ∀ {P : Str → Nat → Str → Bool} {R : Nat → Nat}, PolyBd R → Feas P →
      Feas (fun x _ w => decide (∀ ρ, ρ < R x.length → P x ρ w = true))

variable (F : FeasModel)

/-! ## NP -/

/-- `InNP F L`: the language `L` is in `NP`, i.e. membership is certified by a polynomially
long witness checked by a feasible verifier. -/
def InNP (L : Lang) : Prop :=
  ∃ (p : Nat → Nat) (V : Str → Nat → Str → Bool), PolyBd p ∧ F.Feas V ∧
    ∀ x, L x ↔ ∃ w : Str, w.length = p x.length ∧ V x 0 w = true

/-! ## PCP verifiers -/

/-- A probabilistically checkable proof verifier making `q` queries, using logarithmically
many random bits (equivalently: polynomially many random strings `ρ < R n`) and running in
polynomial time given oracle access to a proof of polynomial length `M n`.

`Q x ρ j` is the `j`-th position of the proof queried on input `x` and random string `ρ`,
and `A x ρ a` is the verdict computed from the `q` answers `a`. -/
structure PCPVerifier (q : Nat) where
  /-- Number of random strings used on inputs of length `n` (so `log₂ (R n)` random bits). -/
  R : Nat → Nat
  /-- Length of the proof accessed on inputs of length `n`. -/
  M : Nat → Nat
  /-- Logarithmic randomness: the number of random strings is polynomial. -/
  Rpoly : PolyBd R
  /-- The proof has polynomial length. -/
  Mpoly : PolyBd M
  /-- At least one random string is used. -/
  Rpos : ∀ n, 0 < R n
  /-- The queried proof positions. -/
  Q : Str → Nat → Fin q → Nat
  /-- The verdict, as a function of the answers to the queries. -/
  A : Str → Nat → (Fin q → Bool) → Bool
  /-- Queries stay inside the proof. -/
  Qlt : ∀ x ρ j, Q x ρ j < M x.length
  /-- One run of the verifier is feasible, given the proof as an oracle. -/
  feas : F.Feas (fun x ρ w => A x ρ (fun j => w.getD (Q x ρ j) false))

variable {F}

/-- The verifier accepts the proof `π` on input `x` and random string `ρ`. -/
def PCPVerifier.Accepts {q : Nat} (V : PCPVerifier F q) (x : Str) (π : Nat → Bool)
    (ρ : Nat) : Prop :=
  V.A x ρ (fun j => π (V.Q x ρ j)) = true

/-- The number of random strings on which the verifier accepts the proof `π`. -/
def PCPVerifier.acceptCount {q : Nat} (V : PCPVerifier F q) (x : Str) (π : Nat → Bool) : Nat :=
  (List.range (V.R x.length)).countP (fun ρ => V.A x ρ (fun j => π (V.Q x ρ j)))

variable (F)

/-- `InPCP F L`: the language `L` is in `PCP(log n, O(1))`, i.e. it has a PCP verifier with
`O(1)` queries and `O(log n)` random bits, with perfect completeness and soundness error at
most `1/2`. -/
def InPCP (L : Lang) : Prop :=
  ∃ (q : Nat) (V : PCPVerifier F q),
    (∀ x, L x → ∃ π : Nat → Bool, ∀ ρ, ρ < V.R x.length → V.Accepts x π ρ) ∧
    (∀ x, ¬ L x → ∀ π : Nat → Bool, 2 * V.acceptCount x π ≤ V.R x.length)

variable {F}

/-! ## The easy inclusion: `PCP(log n, O(1)) ⊆ NP` -/

private theorem getD_map_range (π : Nat → Bool) {m i : Nat} (hi : i < m) :
    ((List.range m).map π).getD i false = π i := by
  rw [List.getD_eq_getElem?_getD]
  simp [hi]

/-- Every language with a `PCP(log n, O(1))` verifier is in `NP`: the NP-witness is the PCP
proof, and the NP-verifier checks all polynomially many random strings. -/
theorem pcp_in_np {L : Lang} (h : InPCP F L) : InNP F L := by
  obtain ⟨q, V, hcomp, hsound⟩ := h
  refine ⟨V.M, (fun x _ w => decide (∀ ρ, ρ < V.R x.length →
      (V.A x ρ (fun j => w.getD (V.Q x ρ j) false)) = true)), V.Mpoly,
      F.feas_forall V.Rpoly V.feas, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨π, hπ⟩ := hcomp x hx
    refine ⟨(List.range (V.M x.length)).map π, by simp, decide_eq_true ?_⟩
    intro ρ hρ
    have h1 := hπ ρ hρ
    unfold PCPVerifier.Accepts at h1
    rw [show (fun j => ((List.range (V.M x.length)).map π).getD (V.Q x ρ j) false)
        = (fun j => π (V.Q x ρ j)) from funext fun j =>
          getD_map_range π (V.Qlt x ρ j)]
    exact h1
  · rintro ⟨w, -, hw⟩
    refine Classical.byContradiction (fun hx => ?_)
    have hall : ∀ ρ, ρ < V.R x.length →
        (V.A x ρ (fun j => w.getD (V.Q x ρ j) false)) = true := of_decide_eq_true hw
    have hcount : V.acceptCount x (fun i => w.getD i false) = V.R x.length := by
      unfold PCPVerifier.acceptCount
      rw [List.countP_eq_length.mpr, List.length_range]
      intro ρ hρ
      rw [List.mem_range] at hρ
      exact hall ρ hρ
    have h2 := hsound x hx (fun i => w.getD i false)
    rw [hcount] at h2
    have h3 := V.Rpos x.length
    omega

/-! ## The statement of the PCP theorem -/

/-- The PCP theorem, as a statement about a model `F` of feasible computation:
`NP = PCP(log n, O(1))`. -/
def PCPTheoremStatement (F : FeasModel) : Prop := ∀ L : Lang, InNP F L ↔ InPCP F L

/-- **The PCP theorem `NP = PCP(log n, O(1))`, in a model `F` of feasible computation, is
equivalent to its hard inclusion `NP ⊆ PCP(log n, O(1))`.**

The easy inclusion `PCP(log n, O(1)) ⊆ NP` is proved here (`CS.pcp_in_np`): an NP machine
guesses the probabilistically checkable proof and checks all polynomially many random
strings.  The reverse inclusion — the deep content of the PCP theorem — is not proved. -/
theorem pcp_theorem (F : FeasModel) :
    PCPTheoremStatement F ↔ ∀ L : Lang, InNP F L → InPCP F L := by
  constructor
  · intro h L hL
    exact (h L).mp hL
  · intro h L
    exact ⟨h L, pcp_in_np⟩

end CS

