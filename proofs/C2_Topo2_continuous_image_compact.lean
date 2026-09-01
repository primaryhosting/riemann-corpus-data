import Mathlib
open Topology Filter
namespace C2.Topo2
theorem continuous_image_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (s : Set X) (hs : IsCompact s) : IsCompact (f '' s) :=
  hs.image hf
theorem compact_closed_bounded (s : Set ℝ) (hs : IsCompact s) : IsClosed s ∧ Bornology.IsBounded s :=
  ⟨hs.isClosed, hs.isBounded⟩
theorem connected_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (s : Set X) (hs : IsConnected s) : IsConnected (f '' s) :=
  hs.image f hf.continuousOn
end C2.Topo2

