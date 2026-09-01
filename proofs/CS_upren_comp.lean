import Mathlib

/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term where
  | var : ℕ → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

/-- Lifting a renaming under a binder. -/
def upren (ξ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Renaming of variables in a term. -/
def ren (ξ : ℕ → ℕ) : Term → Term
  | .var n => .var (ξ n)
  | .app s t => .app (ren ξ s) (ren ξ t)
  | .lam s => .lam (ren (upren ξ) s)

/-- Lifting a substitution under a binder. -/
def upsub (σ : ℕ → Term) : ℕ → Term
  | 0 => .var 0
  | n + 1 => ren Nat.succ (σ n)

/-- Parallel substitution. -/
def subst (σ : ℕ → Term) : Term → Term
  | .var n => σ n
  | .app s t => .app (subst σ s) (subst σ t)
  | .lam s => .lam (subst (upsub σ) s)

/-- Extending a substitution with a new term for the index `0`. -/
def scons (t : Term) (σ : ℕ → Term) : ℕ → Term
  | 0 => t
  | n + 1 => σ n

/-- β-substitution: substitute `t` for the variable bound by the outermost λ. -/
def beta (t s : Term) : Term := subst (scons t Term.var) s

/-! ### Basic substitution calculus -/

theorem upren_comp (ξ ζ : ℕ → ℕ) : upren ξ ∘ upren ζ = upren (ξ ∘ ζ) := by
  funext n
  cases n <;> rfl

theorem ren_ren (ξ ζ : ℕ → ℕ) (s : Term) : ren ξ (ren ζ s) = ren (ξ ∘ ζ) s := by
  induction s generalizing ξ ζ with
  | var n => rfl
  | app a b iha ihb => simp [ren, iha, ihb]
  | lam a ih => simp [ren, ih, upren_comp]

theorem subst_ren (σ : ℕ → Term) (ξ : ℕ → ℕ) (s : Term) :
    subst σ (ren ξ s) = subst (σ ∘ ξ) s := by
  induction s generalizing σ ξ with
  | var n => rfl
  | app a b iha ihb => simp [ren, subst, iha, ihb]
  | lam a ih =>
      have h : upsub σ ∘ upren ξ = upsub (σ ∘ ξ) := by
        funext n; cases n <;> rfl
      simp [ren, subst, ih, h]

theorem ren_subst (ξ : ℕ → ℕ) (σ : ℕ → Term) (s : Term) :
    ren ξ (subst σ s) = subst (fun n => ren ξ (σ n)) s := by
  induction s generalizing ξ σ with
  | var n => rfl
  | app a b iha ihb => simp [ren, subst, iha, ihb]
  | lam a ih =>
      have h : (fun n => ren (upren ξ) (upsub σ n)) = upsub (fun n => ren ξ (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ m =>
            show ren (upren ξ) (ren Nat.succ (σ m)) = ren Nat.succ (ren ξ (σ m))
            rw [ren_ren, ren_ren]
            congr 1
      simp [ren, subst, ih, h]

theorem subst_subst (τ σ : ℕ → Term) (s : Term) :
    subst τ (subst σ s) = subst (fun n => subst τ (σ n)) s := by
  induction s generalizing τ σ with
  | var n => rfl
  | app a b iha ihb => simp [subst, iha, ihb]
  | lam a ih =>
      have h : (fun n => subst (upsub τ) (upsub σ n)) = upsub (fun n => subst τ (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ m =>
            show subst (upsub τ) (ren Nat.succ (σ m)) = ren Nat.succ (subst τ (σ m))
            rw [subst_ren, ren_subst]
            rfl
      simp [subst, ih, h]

theorem subst_var (s : Term) : subst Term.var s = s := by
  induction s with
  | var n => rfl
  | app a b iha ihb => simp [subst, iha, ihb]
  | lam a ih =>
      have h : upsub Term.var = Term.var := by
        funext n; cases n <;> rfl
      simp [subst, h, ih]

/-- Pushing a substitution through a β-redex contraction. -/
theorem subst_beta (σ : ℕ → Term) (a b : Term) :
    subst σ (beta b a) = beta (subst σ b) (subst (upsub σ) a) := by
  unfold beta
  rw [subst_subst, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ m =>
      show σ m = subst (scons (subst σ b) Term.var) (ren Nat.succ (σ m))
      rw [subst_ren]
      exact (subst_var (σ m)).symm

/-! ### Parallel reduction -/

/-- One-step parallel β-reduction. -/
inductive Pstep : Term → Term → Prop where
  | var (n : ℕ) : Pstep (.var n) (.var n)
  | app {s s' t t' : Term} : Pstep s s' → Pstep t t' → Pstep (.app s t) (.app s' t')
  | lam {s s' : Term} : Pstep s s' → Pstep (.lam s) (.lam s')
  | beta {s s' t t' : Term} : Pstep s s' → Pstep t t' → Pstep (.app (.lam s) t) (beta t' s')

theorem Pstep.refl (s : Term) : Pstep s s := by
  induction s with
  | var n => exact Pstep.var n
  | app a b iha ihb => exact Pstep.app iha ihb
  | lam a ih => exact Pstep.lam ih

theorem Pstep.ren {s t : Term} (h : Pstep s t) (ξ : ℕ → ℕ) :
    Pstep (CS.ren ξ s) (CS.ren ξ t) := by
  induction h generalizing ξ with
  | var n => exact Pstep.var _
  | app _ _ iha ihb => exact Pstep.app (iha ξ) (ihb ξ)
  | lam _ ih => exact Pstep.lam (ih (upren ξ))
  | @beta a a' b b' _ _ iha ihb =>
      have key : CS.ren ξ (CS.beta b' a') = CS.beta (CS.ren ξ b') (CS.ren (upren ξ) a') := by
        unfold CS.beta
        rw [ren_subst, subst_ren]
        congr 1
        funext n
        cases n with
        | zero => rfl
        | succ m => rfl
      rw [show CS.ren ξ (Term.app (Term.lam a) b)
            = Term.app (Term.lam (CS.ren (upren ξ) a)) (CS.ren ξ b) from rfl, key]
      exact Pstep.beta (iha (upren ξ)) (ihb ξ)

theorem Pstep.upsub {σ τ : ℕ → Term} (h : ∀ n, Pstep (σ n) (τ n)) :
    ∀ n, Pstep (CS.upsub σ n) (CS.upsub τ n) := by
  intro n
  cases n with
  | zero => exact Pstep.var 0
  | succ m => exact (h m).ren Nat.succ

theorem Pstep.subst {s t : Term} (h : Pstep s t) {σ τ : ℕ → Term}
    (hσ : ∀ n, Pstep (σ n) (τ n)) : Pstep (CS.subst σ s) (CS.subst τ t) := by
  induction h generalizing σ τ with
  | var n => exact hσ n
  | app _ _ iha ihb => exact Pstep.app (iha hσ) (ihb hσ)
  | lam _ ih => exact Pstep.lam (ih (Pstep.upsub hσ))
  | @beta a a' b b' _ _ iha ihb =>
      rw [show CS.subst σ (Term.app (Term.lam a) b)
            = Term.app (Term.lam (CS.subst (CS.upsub σ) a)) (CS.subst σ b) from rfl,
        subst_beta]
      exact Pstep.beta (iha (Pstep.upsub hσ)) (ihb hσ)

theorem Pstep.beta_congr {a a' b b' : Term} (ha : Pstep a a') (hb : Pstep b b') :
    Pstep (CS.beta b a) (CS.beta b' a') := by
  refine ha.subst ?_
  intro n
  cases n with
  | zero => exact hb
  | succ m => exact Pstep.var m

theorem Pstep.lam_inv {a u : Term} (h : Pstep (.lam a) u) :
    ∃ a', u = .lam a' ∧ Pstep a a' := by
  cases h with
  | lam h' => exact ⟨_, rfl, h'⟩

/-- Sanity check: the identity applied to a variable takes a genuine β-step. -/
example : Pstep (.app (.lam (.var 0)) (.var 1)) (.var 1) :=
  Pstep.beta (Pstep.var 0) (Pstep.var 1)

/-! ### Complete development -/

/-- The complete development of a term: contract all β-redexes present in it. -/
def cd : Term → Term
  | .var n => .var n
  | .app (.lam s) t => beta (cd t) (cd s)
  | .app s t => .app (cd s) (cd t)
  | .lam s => .lam (cd s)

theorem cd_app_lam (s t : Term) : cd (.app (.lam s) t) = beta (cd t) (cd s) := rfl

theorem cd_app_var (n : ℕ) (t : Term) :
    cd (.app (.var n) t) = .app (.var n) (cd t) := rfl

theorem cd_app_app (a b t : Term) :
    cd (.app (.app a b) t) = .app (cd (.app a b)) (cd t) := rfl

/-- Takahashi's triangle property: every parallel reduct of `s` reduces to the
complete development of `s`. -/
theorem Pstep.triangle {s t : Term} (h : Pstep s t) : Pstep t (cd s) := by
  induction h with
  | var n => exact Pstep.var n
  | @app a a' b b' hab _ iha ihb =>
      cases a with
      | var n => rw [cd_app_var]; exact Pstep.app iha ihb
      | app c d => rw [cd_app_app]; exact Pstep.app iha ihb
      | lam c =>
          obtain ⟨c', rfl, _⟩ := hab.lam_inv
          rw [cd_app_lam]
          obtain ⟨e, he, hce⟩ := iha.lam_inv
          have hcd : cd (Term.lam c) = Term.lam (cd c) := rfl
          rw [hcd] at he
          have he' : cd c = e := by injection he
          subst he'
          exact Pstep.beta hce ihb
  | lam _ ih => exact Pstep.lam ih
  | @beta a a' b b' _ _ iha ihb =>
      rw [cd_app_lam]
      exact Pstep.beta_congr iha ihb

/-- **Diamond property of parallel β-reduction.**  If a λ-term `s` reduces in one
parallel β-step to both `t` and `u`, then `t` and `u` have a common one-step
parallel reduct. -/
theorem church_rosser_beta_diamond {s t u : Term} (h₁ : Pstep s t) (h₂ : Pstep s u) :
    ∃ v, Pstep t v ∧ Pstep u v :=
  ⟨cd s, h₁.triangle, h₂.triangle⟩

end CS

