/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-! ## Untyped λ-terms in de Bruijn representation -/

/-- Untyped λ-terms with de Bruijn indices. -/
inductive Lam : Type
  | var : ℕ → Lam
  | app : Lam → Lam → Lam
  | lam : Lam → Lam
  deriving DecidableEq

namespace Lam

/-- Lift a renaming under a binder. -/
def upr (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => r i + 1

/-- Apply a renaming of de Bruijn indices to a term. -/
def ren (r : ℕ → ℕ) : Lam → Lam
  | var i => var (r i)
  | app a b => app (ren r a) (ren r b)
  | lam a => lam (ren (upr r) a)

/-- Lift a substitution under a binder. -/
def up (σ : ℕ → Lam) : ℕ → Lam
  | 0 => var 0
  | i + 1 => ren Nat.succ (σ i)

/-- Apply a (parallel) substitution to a term. -/
def sub (σ : ℕ → Lam) : Lam → Lam
  | var i => σ i
  | app a b => app (sub σ a) (sub σ b)
  | lam a => lam (sub (up σ) a)

/-- Extend a substitution with a new term for index `0`. -/
def cons (t : Lam) (σ : ℕ → Lam) : ℕ → Lam
  | 0 => t
  | i + 1 => σ i

/-- The substitution performed by a β-step: `(λ a) b ↝ beta a b`. -/
def beta (a b : Lam) : Lam := sub (cons b var) a

/-! ### The σ-algebra laws for renaming and substitution -/

theorem upr_comp (r s : ℕ → ℕ) : ∀ i, upr r (upr s i) = upr (fun j => r (s j)) i
  | 0 => rfl
  | _ + 1 => rfl

theorem ren_ren (r s : ℕ → ℕ) :
    ∀ t : Lam, ren r (ren s t) = ren (fun j => r (s j)) t
  | var _ => rfl
  | app a b => by simp [ren, ren_ren r s a, ren_ren r s b]
  | lam a => by
      simp only [ren, ren_ren (upr r) (upr s) a]
      exact congrArg lam (congrArg (fun f => ren f a) (funext (upr_comp r s)))

theorem sub_ren (σ : ℕ → Lam) (r : ℕ → ℕ) :
    ∀ t : Lam, sub σ (ren r t) = sub (fun j => σ (r j)) t
  | var _ => rfl
  | app a b => by simp [ren, sub, sub_ren σ r a, sub_ren σ r b]
  | lam a => by
      simp only [ren, sub, sub_ren (up σ) (upr r) a]
      refine congrArg lam (congrArg (fun f => sub f a) (funext ?_))
      rintro (_ | i) <;> rfl

theorem ren_sub (r : ℕ → ℕ) (σ : ℕ → Lam) :
    ∀ t : Lam, ren r (sub σ t) = sub (fun j => ren r (σ j)) t
  | var _ => rfl
  | app a b => by simp [ren, sub, ren_sub r σ a, ren_sub r σ b]
  | lam a => by
      simp only [ren, sub, ren_sub (upr r) (up σ) a]
      refine congrArg lam (congrArg (fun f => sub f a) (funext ?_))
      rintro (_ | i)
      · rfl
      · simp only [up, ren_ren]
        rfl

theorem sub_sub (σ τ : ℕ → Lam) :
    ∀ t : Lam, sub σ (sub τ t) = sub (fun j => sub σ (τ j)) t
  | var _ => rfl
  | app a b => by simp [sub, sub_sub σ τ a, sub_sub σ τ b]
  | lam a => by
      simp only [sub, sub_sub (up σ) (up τ) a]
      refine congrArg lam (congrArg (fun f => sub f a) (funext ?_))
      rintro (_ | i)
      · rfl
      · simp only [up, sub_ren, ren_sub]
        rfl

theorem sub_var : ∀ t : Lam, sub var t = t
  | var _ => rfl
  | app a b => by simp [sub, sub_var a, sub_var b]
  | lam a => by
      simp only [sub]
      refine congrArg lam ?_
      have : up var = var := by funext i; cases i <;> rfl
      rw [this, sub_var a]

/-- Renaming commutes with a single β-substitution. -/
theorem ren_beta (r : ℕ → ℕ) (a b : Lam) :
    ren r (beta a b) = beta (ren (upr r) a) (ren r b) := by
  simp only [beta, ren_sub, sub_ren]
  refine congrArg (fun f => sub f a) (funext ?_)
  rintro (_ | i) <;> rfl

/-- Substitution commutes with a single β-substitution. -/
theorem sub_beta (σ : ℕ → Lam) (a b : Lam) :
    sub σ (beta a b) = beta (sub (up σ) a) (sub σ b) := by
  simp only [beta, sub_sub]
  refine congrArg (fun f => sub f a) (funext ?_)
  rintro (_ | i)
  · rfl
  · simp only [cons, up, sub_ren]
    exact (sub_var _).symm ▸ rfl

/-! ## Parallel one-step β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Lam → Lam → Prop
  | var (i : ℕ) : Par (var i) (var i)
  | app {a a' b b' : Lam} : Par a a' → Par b b' → Par (app a b) (app a' b')
  | lam {a a' : Lam} : Par a a' → Par (lam a) (lam a')
  | beta {a a' b b' : Lam} : Par a a' → Par b b' → Par (app (lam a) b) (beta a' b')

theorem Par.refl : ∀ t : Lam, Par t t
  | var i => Par.var i
  | app a b => Par.app (Par.refl a) (Par.refl b)
  | lam a => Par.lam (Par.refl a)

theorem Par.ren {a b : Lam} (h : Par a b) : ∀ r : ℕ → ℕ, Par (Lam.ren r a) (Lam.ren r b) := by
  induction h with
  | var i => intro r; exact Par.var _
  | app _ _ iha ihb => intro r; exact Par.app (iha r) (ihb r)
  | lam _ ih => intro r; exact Par.lam (ih _)
  | beta _ _ iha ihb =>
      intro r
      rw [Lam.ren_beta]
      exact Par.beta (iha (upr r)) (ihb r)

theorem Par.up {σ τ : ℕ → Lam} (h : ∀ i, Par (σ i) (τ i)) :
    ∀ i, Par (Lam.up σ i) (Lam.up τ i) := by
  rintro (_ | i)
  · exact Par.var 0
  · exact (h i).ren Nat.succ

theorem Par.sub {a b : Lam} (h : Par a b) :
    ∀ {σ τ : ℕ → Lam}, (∀ i, Par (σ i) (τ i)) → Par (Lam.sub σ a) (Lam.sub τ b) := by
  induction h with
  | var i => intro σ τ hst; exact hst i
  | app _ _ iha ihb => intro σ τ hst; exact Par.app (iha hst) (ihb hst)
  | lam _ ih => intro σ τ hst; exact Par.lam (ih (Par.up hst))
  | beta _ _ iha ihb =>
      intro σ τ hst
      rw [Lam.sub_beta]
      exact Par.beta (iha (Par.up hst)) (ihb hst)

/-- Parallel reduction is compatible with β-substitution. -/
theorem Par.betaCongr {a a' b b' : Lam} (ha : Par a a') (hb : Par b b') :
    Par (Lam.beta a b) (Lam.beta a' b') := by
  refine ha.sub ?_
  rintro (_ | i)
  · exact hb
  · exact Par.var i

/-! ## Takahashi's complete development -/

/-- The complete development of a term: contract all β-redexes present. -/
def dev : Lam → Lam
  | var i => var i
  | app (lam a) b => beta (dev a) (dev b)
  | app a b => app (dev a) (dev b)
  | lam a => lam (dev a)

theorem dev_app_lam (a b : Lam) : dev (app (lam a) b) = beta (dev a) (dev b) := rfl

theorem dev_app_var (i : ℕ) (b : Lam) : dev (app (var i) b) = app (var i) (dev b) := rfl

theorem dev_app_app (a₁ a₂ b : Lam) :
    dev (app (app a₁ a₂) b) = app (dev (app a₁ a₂)) (dev b) := rfl

/-- Takahashi's key "triangle" property: every parallel reduct of `t` parallel-reduces
to the complete development of `t`. -/
theorem Par.triangle {t u : Lam} (h : Par t u) : Par u (dev t) := by
  induction h with
  | var i => exact Par.var i
  | @app a a' b b' hab _ iha ihb =>
      cases a with
      | var i =>
          cases hab
          rw [dev_app_var]
          exact Par.app (Par.var i) ihb
      | app a₁ a₂ =>
          rw [dev_app_app]
          exact Par.app iha ihb
      | lam c =>
          cases hab with
          | lam hc =>
              rw [dev_app_lam]
              rename_i c' _
              have : Par (Lam.lam c') (Lam.lam (dev c)) := iha
              cases this with
              | lam hc' => exact Par.beta hc' ihb
  | lam _ ih => exact Par.lam ih
  | beta _ _ iha ihb =>
      rw [dev_app_lam]
      exact Par.betaCongr iha ihb

end Lam

/-- **Church–Rosser, diamond property for parallel β-reduction.**
One-step parallel β-reduction in the untyped λ-calculus has the diamond property:
if `t` parallel-reduces to both `u` and `v`, then `u` and `v` have a common
parallel reduct. -/
theorem church_rosser_beta_diamond {t u v : Lam} (hu : Lam.Par t u) (hv : Lam.Par t v) :
    ∃ w : Lam, Lam.Par u w ∧ Lam.Par v w :=
  ⟨Lam.dev t, hu.triangle, hv.triangle⟩

end CS

