module

public import GuibasStolfi.Subdivision.Prelim
public import Mathlib.Order.Setoid.Partition

@[expose] public section

open Set Filter Topology Metric

namespace GuibasStolfi

/-! ## boundary circle -/
section BoundaryPaths

/-- the circle S¹ -/
abbrev UnitCircle := Metric.sphere (0 : Plane) 1

/-- data for finite decomposition of S¹ -/
structure SimplePath where
  m : ℕ
  elem : Fin (m + 1) → Set UnitCircle
  injective : Function.Injective elem
  isPartition : Setoid.IsPartition (Set.range elem)
  isPoint_or_arc :
    ∀ i, IsPoint (elem i) ∨ (IsOpen (elem i) ∧ IsLine (elem i))
  adjacent : ∀ i, IsConnected (elem i ∪ elem (i + 1))

end BoundaryPaths

/-! homoemorphisms on subsets -/
section HomeomorphOn

variable {X Y : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- helper -/
def HomeomorphOn (f : X → Y) (s : Set X) (t : Set Y) : Prop :=
  ∃ h : s ≃ₜ t, ∀ x : s, (h x : Y) = f x

end HomeomorphOn

/-! ## Definition 1.1 Subdivision -/


end GuibasStolfi
