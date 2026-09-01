import Mathlib
namespace C6.T4
theorem union_open {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := hs.union ht
theorem inter_closed {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ t) := hs.inter ht
theorem compact_union {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := hs.union ht
end C6.T4

