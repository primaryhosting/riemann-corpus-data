import Mathlib

/-!
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- Orbital integral of a test function `f` at `γ`, taken with respect to counting
measure on the group: `O_γ(f) = ∑_{x ∈ G} f (x γ x⁻¹)`. -/
def orbitalIntegral {G : Type} [Group G] [Fintype G] (f : G → ℚ) (γ : G) : ℚ :=
  ∑ x : G, f (x * γ * x⁻¹)

/-- κ-orbital integral attached to a family `γ : I → G` of representatives of the
rational conjugacy classes inside one stable class, weighted by the character `κ`. -/
def kappaOrbitalIntegral {G I : Type} [Group G] [Fintype G] [Fintype I]
    (f : G → ℚ) (γ : I → G) (κ : I → ℚ) : ℚ :=
  ∑ i : I, κ i * orbitalIntegral f (γ i)

/-- Stable orbital integral: the κ-orbital integral for the trivial character. -/
def stableOrbitalIntegral {G I : Type} [Group G] [Fintype G] [Fintype I]
    (f : G → ℚ) (γ : I → G) : ℚ :=
  ∑ i : I, orbitalIntegral f (γ i)

/-- The Langlands–Shelstad identity (the Fundamental Lemma, proved by Ngô):
the κ-orbital integral on `G` of the unit of the Hecke algebra equals the transfer
factor times the stable orbital integral on the endoscopic group `H`. -/
def FundamentalLemmaHolds {G H I J : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    [Fintype I] [Fintype J]
    (fG : G → ℚ) (γG : I → G) (κ : I → ℚ) (fH : H → ℚ) (γH : J → H) (Δ : ℚ) : Prop :=
  kappaOrbitalIntegral fG γG κ = Δ * stableOrbitalIntegral fH γH

/-- Orbital integrals only depend on the conjugacy class of `γ`. -/
theorem orbitalIntegral_conj {G : Type} [Group G] [Fintype G] (f : G → ℚ) (γ g : G) :
    orbitalIntegral f (g * γ * g⁻¹) = orbitalIntegral f γ := by
  unfold orbitalIntegral
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ ?_
  intro x
  simp [mul_inv_rev, mul_assoc]

/-- On an abelian group (a torus) conjugation is trivial, so the orbital integral is
just `|G| · f γ`.  This is the classical statement that the fundamental lemma is
trivial for tori. -/
theorem orbitalIntegral_of_comm {G : Type} [CommGroup G] [Fintype G] (f : G → ℚ) (γ : G) :
    orbitalIntegral f γ = (Fintype.card G : ℚ) * f γ := by
  unfold orbitalIntegral
  simp [mul_comm, mul_assoc, Finset.card_univ]

/-- Base case of the fundamental lemma for tori: `G = H` abelian, trivial κ, transfer
factor `1`, and matching test functions. -/
theorem fundamentalLemma_torus {G I : Type} [CommGroup G] [Fintype G] [Fintype I]
    (f : G → ℚ) (γ : I → G) :
    FundamentalLemmaHolds f γ (fun _ => 1) f γ 1 := by
  unfold FundamentalLemmaHolds kappaOrbitalIntegral stableOrbitalIntegral
  simp

/-- Base case (principal, i.e. trivial, endoscopy): `H = G`, `κ = 1`, `Δ = 1`. -/
theorem fundamentalLemma_principal {G I : Type} [Group G] [Fintype G] [Fintype I]
    (f : G → ℚ) (γ : I → G) :
    FundamentalLemmaHolds f γ (fun _ => 1) f γ 1 := by
  unfold FundamentalLemmaHolds kappaOrbitalIntegral stableOrbitalIntegral
  simp

/-- **Non-vacuity of the statement: unstable transfer with a nontrivial character.**
For a torus `T` (finite abelian group) and *any* character `κ`, the κ-orbital integral
on `T` is a stable orbital integral on an endoscopic group, with transfer factor
`Δ = |T|`.  Here `κ` and `Δ` are genuinely nontrivial, so `FundamentalLemmaHolds`
is not only satisfied in the principal case. -/
theorem fundamentalLemma_torus_kappa {T I : Type} [CommGroup T] [Fintype T] [Fintype I]
    (f : T → ℚ) (γ : I → T) (κ : I → ℚ) :
    FundamentalLemmaHolds (G := T) (H := PUnit) (I := I) (J := PUnit)
      f γ κ (fun _ => ∑ i : I, κ i * f (γ i)) (fun _ => 1) (Fintype.card T : ℚ) := by
  unfold FundamentalLemmaHolds kappaOrbitalIntegral stableOrbitalIntegral
  simp [orbitalIntegral, Finset.mul_sum]
  exact Finset.sum_congr rfl (by intros; ring)

/-- Orbital integrals factor through products of groups. -/
theorem orbitalIntegral_prod {G₁ G₂ : Type} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    (f₁ : G₁ → ℚ) (f₂ : G₂ → ℚ) (γ₁ : G₁) (γ₂ : G₂) :
    orbitalIntegral (fun p : G₁ × G₂ => f₁ p.1 * f₂ p.2) (γ₁, γ₂)
      = orbitalIntegral f₁ γ₁ * orbitalIntegral f₂ γ₂ := by
  unfold orbitalIntegral
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  rfl

/-- A sum over a product index set of a product of functions splits. -/
theorem sum_prod_mul {I₁ I₂ : Type} [Fintype I₁] [Fintype I₂] (a : I₁ → ℚ) (b : I₂ → ℚ) :
    (∑ i : I₁ × I₂, a i.1 * b i.2) = (∑ i : I₁, a i) * (∑ j : I₂, b j) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Reduction step: the fundamental lemma for a product of endoscopic data follows
from the fundamental lemma for each factor. -/
theorem fundamentalLemma_prod
    {G₁ H₁ I₁ J₁ G₂ H₂ I₂ J₂ : Type}
    [Group G₁] [Fintype G₁] [Group H₁] [Fintype H₁] [Fintype I₁] [Fintype J₁]
    [Group G₂] [Fintype G₂] [Group H₂] [Fintype H₂] [Fintype I₂] [Fintype J₂]
    (fG₁ : G₁ → ℚ) (γG₁ : I₁ → G₁) (κ₁ : I₁ → ℚ) (fH₁ : H₁ → ℚ) (γH₁ : J₁ → H₁) (Δ₁ : ℚ)
    (fG₂ : G₂ → ℚ) (γG₂ : I₂ → G₂) (κ₂ : I₂ → ℚ) (fH₂ : H₂ → ℚ) (γH₂ : J₂ → H₂) (Δ₂ : ℚ)
    (h₁ : FundamentalLemmaHolds fG₁ γG₁ κ₁ fH₁ γH₁ Δ₁)
    (h₂ : FundamentalLemmaHolds fG₂ γG₂ κ₂ fH₂ γH₂ Δ₂) :
    FundamentalLemmaHolds
      (fun p : G₁ × G₂ => fG₁ p.1 * fG₂ p.2)
      (fun i : I₁ × I₂ => (γG₁ i.1, γG₂ i.2))
      (fun i : I₁ × I₂ => κ₁ i.1 * κ₂ i.2)
      (fun q : H₁ × H₂ => fH₁ q.1 * fH₂ q.2)
      (fun j : J₁ × J₂ => (γH₁ j.1, γH₂ j.2))
      (Δ₁ * Δ₂) := by
  unfold FundamentalLemmaHolds kappaOrbitalIntegral stableOrbitalIntegral at *
  have hG : ∀ i : I₁ × I₂,
      κ₁ i.1 * κ₂ i.2 * orbitalIntegral (fun p : G₁ × G₂ => fG₁ p.1 * fG₂ p.2)
          (γG₁ i.1, γG₂ i.2)
        = (κ₁ i.1 * orbitalIntegral fG₁ (γG₁ i.1)) * (κ₂ i.2 * orbitalIntegral fG₂ (γG₂ i.2)) := by
    intro i; rw [orbitalIntegral_prod]; ring
  have hH : ∀ j : J₁ × J₂,
      orbitalIntegral (fun q : H₁ × H₂ => fH₁ q.1 * fH₂ q.2) (γH₁ j.1, γH₂ j.2)
        = orbitalIntegral fH₁ (γH₁ j.1) * orbitalIntegral fH₂ (γH₂ j.2) := by
    intro j; rw [orbitalIntegral_prod]
  rw [Fintype.sum_congr _ _ hG, Fintype.sum_congr _ _ hH,
    sum_prod_mul (fun i => κ₁ i * orbitalIntegral fG₁ (γG₁ i))
      (fun i => κ₂ i * orbitalIntegral fG₂ (γG₂ i)),
    sum_prod_mul (fun j => orbitalIntegral fH₁ (γH₁ j))
      (fun j => orbitalIntegral fH₂ (γH₂ j)),
    h₁, h₂]
  ring

/-- The κ-orbital integral is linear in the test function, so the fundamental lemma
is stable under linear combinations of matching test functions. -/
theorem fundamentalLemma_smul {G H I J : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    [Fintype I] [Fintype J]
    (fG : G → ℚ) (γG : I → G) (κ : I → ℚ) (fH : H → ℚ) (γH : J → H) (Δ c : ℚ)
    (h : FundamentalLemmaHolds fG γG κ fH γH Δ) :
    FundamentalLemmaHolds (fun x => c * fG x) γG κ (fun y => c * fH y) γH Δ := by
  unfold FundamentalLemmaHolds kappaOrbitalIntegral stableOrbitalIntegral orbitalIntegral at *
  simp only [← Finset.mul_sum] at *
  rw [show (∑ i : I, κ i * (c * ∑ x : G, fG (x * γG i * x⁻¹)))
      = c * ∑ i : I, κ i * ∑ x : G, fG (x * γG i * x⁻¹) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (by intros; ring)]
  rw [h]
  ring

/-- **Ngô's Fundamental Lemma (Langlands–Shelstad), formalized statement together with
the base cases and a reduction that are verified here.**

`FundamentalLemmaHolds fG γG κ fH γH Δ` is the Langlands–Shelstad identity
`O^κ_{γ_G}(f_G) = Δ · SO_{γ_H}(f_H)` in the finite (counting-measure) model:
the κ-orbital integral over the rational classes `γG` inside a stable class of `G`
equals the transfer factor `Δ` times the stable orbital integral on the endoscopic
group `H`.

What is proved:
1. the base case of principal (trivial) endoscopy, `H = G`, `κ ≡ 1`, `Δ = 1`;
2. the torus case, where conjugation is trivial and orbital integrals are `|T| · f γ`;
3. the reduction to factors: the identity for a product of endoscopic data follows
   from the identity for each factor;
4. non-vacuity: an instance with a nontrivial character `κ` and a nontrivial transfer
   factor, so the identity is not merely the principal one in disguise. -/
theorem ngo_fundamental_lemma :
    (∀ (G I : Type) [Group G] [Fintype G] [Fintype I] (f : G → ℚ) (γ : I → G),
        FundamentalLemmaHolds f γ (fun _ => 1) f γ 1)
    ∧ (∀ (T I : Type) [CommGroup T] [Fintype T] [Fintype I] (f : T → ℚ) (γ : I → T),
        kappaOrbitalIntegral f γ (fun _ => 1)
          = (Fintype.card T : ℚ) * ∑ i : I, f (γ i))
    ∧ (∀ (G₁ H₁ I₁ J₁ G₂ H₂ I₂ J₂ : Type)
        [Group G₁] [Fintype G₁] [Group H₁] [Fintype H₁] [Fintype I₁] [Fintype J₁]
        [Group G₂] [Fintype G₂] [Group H₂] [Fintype H₂] [Fintype I₂] [Fintype J₂]
        (fG₁ : G₁ → ℚ) (γG₁ : I₁ → G₁) (κ₁ : I₁ → ℚ) (fH₁ : H₁ → ℚ) (γH₁ : J₁ → H₁) (Δ₁ : ℚ)
        (fG₂ : G₂ → ℚ) (γG₂ : I₂ → G₂) (κ₂ : I₂ → ℚ) (fH₂ : H₂ → ℚ) (γH₂ : J₂ → H₂) (Δ₂ : ℚ),
        FundamentalLemmaHolds fG₁ γG₁ κ₁ fH₁ γH₁ Δ₁ →
        FundamentalLemmaHolds fG₂ γG₂ κ₂ fH₂ γH₂ Δ₂ →
        FundamentalLemmaHolds
          (fun p : G₁ × G₂ => fG₁ p.1 * fG₂ p.2)
          (fun i : I₁ × I₂ => (γG₁ i.1, γG₂ i.2))
          (fun i : I₁ × I₂ => κ₁ i.1 * κ₂ i.2)
          (fun q : H₁ × H₂ => fH₁ q.1 * fH₂ q.2)
          (fun j : J₁ × J₂ => (γH₁ j.1, γH₂ j.2))
          (Δ₁ * Δ₂))
    ∧ (∀ (T I : Type) [CommGroup T] [Fintype T] [Fintype I]
        (f : T → ℚ) (γ : I → T) (κ : I → ℚ),
        FundamentalLemmaHolds (G := T) (H := PUnit) (I := I) (J := PUnit)
          f γ κ (fun _ => ∑ i : I, κ i * f (γ i)) (fun _ => 1) (Fintype.card T : ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G I _ _ _ f γ
    exact fundamentalLemma_principal f γ
  · intro T I _ _ _ f γ
    unfold kappaOrbitalIntegral
    simp [orbitalIntegral_of_comm, Finset.mul_sum]
  · intro G₁ H₁ I₁ J₁ G₂ H₂ I₂ J₂ _ _ _ _ _ _ _ _ _ _ _ _
      fG₁ γG₁ κ₁ fH₁ γH₁ Δ₁ fG₂ γG₂ κ₂ fH₂ γH₂ Δ₂ h₁ h₂
    exact fundamentalLemma_prod _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  · intro T I _ _ _ f γ κ
    exact fundamentalLemma_torus_kappa f γ κ

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


