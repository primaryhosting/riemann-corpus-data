/-!
# Canonical three-site blocks for the twin-sieve wheel

For a modulus `15 * Q` with `15` coprime to `Q`, the Chinese remainder
equivalence separates the modulo-15 and modulo-`Q` coordinates. The three
modulo-15 lanes `11, 14, 2` form a path under translation by `3`.

This module proves that residues on those lanes have unique coordinates in
`ZMod Q × Fin 3`, and that undirected `3`-step adjacency is exactly adjacency
inside one three-site block. It does not yet identify a deletion mask with the
actual twin-admissible unit predicate or define the compressed Hamiltonian.
-/

import Mathlib
import Brockian.SieveSpectrumCounts

set_option autoImplicit false

namespace Brockian.SieveSpectrumBlocks

noncomputable section

/-- The three modulo-15 lanes in forward `+3` order. -/
def lane15 : Fin 3 -> ZMod 15 := ![11, 14, 2]

/-- The compensating shift in the modulo-`Q` coordinate. -/
def laneShift : Fin 3 -> Nat := ![0, 3, 6]

/-- Chinese remainder coordinates for `15 * Q`. -/
def crt15Q (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    ZMod (15 * Q) ≃+* ZMod 15 × ZMod Q :=
  ZMod.chineseRemainder h15

/-- Site `j` in the potential three-site block indexed by `b`. -/
def blockVertex (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (b : ZMod Q) (j : Fin 3) : ZMod (15 * Q) :=
  (crt15Q Q h15).symm
    (lane15 j, b + (laneShift j : ZMod Q))

private theorem crt15Q_three
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    crt15Q Q h15 (3 : ZMod (15 * Q)) =
      ((3 : ZMod 15), (3 : ZMod Q)) := by
  calc
    crt15Q Q h15 (3 : ZMod (15 * Q)) =
        (3 : ZMod 15 × ZMod Q) := map_natCast (crt15Q Q h15) 3
    _ = ((3 : ZMod 15), (3 : ZMod Q)) := by rfl

@[simp] theorem crt15Q_blockVertex
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (b : ZMod Q) (j : Fin 3) :
    crt15Q Q h15 (blockVertex Q h15 b j) =
      (lane15 j, b + (laneShift j : ZMod Q)) := by
  simp [blockVertex, crt15Q]

/-- The three lane labels are distinct. -/
theorem lane15_injective : Function.Injective lane15 := by
  decide

/-- Potential block coordinates identify a unique wheel residue. -/
theorem blockVertex_injective
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    Function.Injective
      (fun x : ZMod Q × Fin 3 => blockVertex Q h15 x.1 x.2) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ h
  have hcrt := congrArg (crt15Q Q h15) h
  rw [crt15Q_blockVertex, crt15Q_blockVertex] at hcrt
  have hij : i = j := lane15_injective (congrArg Prod.fst hcrt)
  subst j
  have hbc : b = c := add_right_cancel (congrArg Prod.snd hcrt)
  subst c
  rfl

/-- The first forward step remains inside the block. -/
theorem blockVertex_step01
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) (b : ZMod Q) :
    blockVertex Q h15 b 1 = blockVertex Q h15 b 0 + 3 := by
  apply (crt15Q Q h15).injective
  rw [map_add, crt15Q_blockVertex, crt15Q_blockVertex, crt15Q_three]
  apply Prod.ext
  · change lane15 1 = lane15 0 + 3
    decide
  · simp [laneShift]

/-- The second forward step remains inside the block. -/
theorem blockVertex_step12
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) (b : ZMod Q) :
    blockVertex Q h15 b 2 = blockVertex Q h15 b 1 + 3 := by
  apply (crt15Q Q h15).injective
  rw [map_add, crt15Q_blockVertex, crt15Q_blockVertex, crt15Q_three]
  apply Prod.ext
  · change lane15 2 = lane15 1 + 3
    decide
  · change b + 6 = b + 3 + 3
    ring

/-- A residue belongs to one of the three potential lanes. -/
def IsLaneSite (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (a : ZMod (15 * Q)) : Prop :=
  ∃ j : Fin 3, (crt15Q Q h15 a).1 = lane15 j

/-- Every lane residue has unique block coordinates. -/
theorem existsUnique_blockVertex_of_lane
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (a : ZMod (15 * Q)) (ha : IsLaneSite Q h15 a) :
    ∃! x : ZMod Q × Fin 3, blockVertex Q h15 x.1 x.2 = a := by
  rcases ha with ⟨j, hj⟩
  let b : ZMod Q :=
    (crt15Q Q h15 a).2 - (laneShift j : ZMod Q)
  have hrep : blockVertex Q h15 b j = a := by
    apply (crt15Q Q h15).injective
    rw [crt15Q_blockVertex]
    ext
    · simpa using hj.symm
    · simp [b]
  refine ⟨(b, j), hrep, ?_⟩
  intro y hy
  apply blockVertex_injective Q h15
  calc
    blockVertex Q h15 y.1 y.2 = a := hy
    _ = blockVertex Q h15 b j := hrep.symm

/-- Residues on the three lanes, as a subtype. -/
def LaneSite (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :=
  {a : ZMod (15 * Q) // IsLaneSite Q h15 a}

/-- Forget block coordinates while retaining the lane witness. -/
def blockCoordMap
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    ZMod Q × Fin 3 -> LaneSite Q h15 := fun x =>
  ⟨blockVertex Q h15 x.1 x.2, x.2, by simp⟩

/-- The block-coordinate map is bijective. -/
theorem blockCoordMap_bijective
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    Function.Bijective (blockCoordMap Q h15) := by
  constructor
  · intro x y hxy
    apply blockVertex_injective Q h15
    exact congrArg Subtype.val hxy
  · intro y
    rcases existsUnique_blockVertex_of_lane Q h15 y.1 y.2 with
      ⟨x, hx, _⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- Canonical equivalence between blocks and modulo-15 lane residues. -/
def blockCoordEquiv
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    (ZMod Q × Fin 3) ≃ LaneSite Q h15 :=
  Equiv.ofBijective (blockCoordMap Q h15) (blockCoordMap_bijective Q h15)

/-- Adjacency in the potential three-site path. -/
def Path3Adj (i j : Fin 3) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)

/-- Adjacency in block coordinates. -/
def BlockAdj {Q : Nat} (x y : ZMod Q × Fin 3) : Prop :=
  x.1 = y.1 ∧ Path3Adj x.2 y.2

/-- Undirected wheel adjacency by a step of `3`. -/
def WheelAdj {Q : Nat} [NeZero Q]
    (a b : ZMod (15 * Q)) : Prop :=
  b = a + 3 ∨ a = b + 3

/-- The only forward transitions between lane labels are `0 -> 1` and
`1 -> 2`. -/
theorem lane15_forward_iff (i j : Fin 3) :
    lane15 j = lane15 i + 3 ↔
      ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- A forward `+3` step between potential sites fixes the block index. -/
theorem forward_step_classification
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (b c : ZMod Q) (i j : Fin 3)
    (h : blockVertex Q h15 c j = blockVertex Q h15 b i + 3) :
    b = c ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)) := by
  have hcrt := congrArg (crt15Q Q h15) h
  have hpair :
      (lane15 j, c + (laneShift j : ZMod Q)) =
        (lane15 i + 3, b + (laneShift i : ZMod Q) + 3) := by
    rw [crt15Q_blockVertex, map_add, crt15Q_blockVertex, crt15Q_three] at hcrt
    exact hcrt
  have hlane : lane15 j = lane15 i + 3 := congrArg Prod.fst hpair
  rcases (lane15_forward_iff i j).mp hlane with hij | hij
  · rcases hij with ⟨rfl, rfl⟩
    have hbc : c = b := by
      simpa [laneShift] using congrArg Prod.snd hpair
    exact ⟨hbc.symm, Or.inl ⟨rfl, rfl⟩⟩
  · rcases hij with ⟨rfl, rfl⟩
    have hq : c + 6 = b + 3 + 3 := by
      simpa [laneShift] using congrArg Prod.snd hpair
    have hq' : c + 6 = b + 6 := by
      calc
        c + 6 = b + 3 + 3 := hq
        _ = b + 6 := by ring
    exact ⟨(add_right_cancel hq').symm, Or.inr ⟨rfl, rfl⟩⟩

/-- Block adjacency maps to wheel adjacency. -/
theorem blockAdj_implies_wheelAdj
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (x y : ZMod Q × Fin 3) (hxy : BlockAdj x y) :
    WheelAdj (blockVertex Q h15 x.1 x.2)
      (blockVertex Q h15 y.1 y.2) := by
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  rcases hxy with ⟨rfl, hpath⟩
  rcases hpath with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (blockVertex_step01 Q h15 b)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr (blockVertex_step01 Q h15 b)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inl (blockVertex_step12 Q h15 b)
  · rcases h with ⟨rfl, rfl⟩
    exact Or.inr (blockVertex_step12 Q h15 b)

/-- Wheel adjacency between lane sites is exactly adjacency inside one block. -/
theorem wheelAdj_iff_blockAdj
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (x y : ZMod Q × Fin 3) :
    WheelAdj (blockVertex Q h15 x.1 x.2)
        (blockVertex Q h15 y.1 y.2) ↔ BlockAdj x y := by
  constructor
  · rintro (h | h)
    · rcases forward_step_classification Q h15 x.1 y.1 x.2 y.2 h with
        ⟨hbc, hp⟩
      refine ⟨hbc, ?_⟩
      exact hp.elim (fun z => Or.inl z)
        (fun z => Or.inr (Or.inr (Or.inl z)))
    · rcases forward_step_classification Q h15 y.1 x.1 y.2 x.2 h with
        ⟨hcb, hp⟩
      refine ⟨hcb.symm, ?_⟩
      exact hp.elim
        (fun z => Or.inr (Or.inl ⟨z.2, z.1⟩))
        (fun z => Or.inr (Or.inr (Or.inr ⟨z.2, z.1⟩)))
  · exact blockAdj_implies_wheelAdj Q h15 x y

end

end Brockian.SieveSpectrumBlocks
