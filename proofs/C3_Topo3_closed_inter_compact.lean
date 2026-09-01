import Mathlib
namespace C3.Topo3

/-- The intersection of a compact set with a closed set is compact. -/
theorem closed_inter_compact {X : Type*} [TopologicalSpace X] (s t : Set X)
    (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) :=
  hs.inter_right ht

/-- Every subset of a finite topological space is compact. -/
theorem discrete_finite_compact {X : Type*} [TopologicalSpace X] [Fintype X] (s : Set X) :
    IsCompact s :=
  (Set.toFinite s).isCompact

/-- Constant maps are continuous. -/
theorem continuous_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (c : Y) :
    Continuous (fun _ : X => c) :=
  _root_.continuous_const

end C3.Topo3

