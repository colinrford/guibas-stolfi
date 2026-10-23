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
section Subdivisions

structure Subdivision (M : Type*) [TopologicalSpace M] where
  vertices : Set (Set M)
  edges : Set (Set M)
  faces : Set (Set M)
  finite_vertices : vertices.Finite
  finite_edges : edges.Finite
  finite_faces : faces.Finite
  isTwoManifold : IsTwoManifold M
  isPartition : Setoid.IsPartition (vertices ∪ edges ∪ faces)
  /-- S1 -/
  isPoint_of_mem : ∀ v ∈ vertices, IsPoint v
  /-- S2 -/
  isLine_of_mem : ∀ e ∈ edges, IsLine e
  /-- S3 -/
  isDisk_of_mem : ∀ F ∈ faces, IsDisk F
  /-- S4 -/
  boundary : ∀ F ∈ faces, ∃ (π : SimplePath) (ϕ : Plane → M),
    ContinuousOn ϕ (Metric.closedBall 0 1) ∧
    ϕ '' Metric.closedBall 0 1 = closure F ∧
    HomeomorphOn ϕ (Metric.ball 0 1) F ∧
    (∀ i, IsLine (π.elem i) →
      ∃ e ∈ edges,
        HomeomorphOn ϕ (Subtype.val '' π.elem i) e) ∧
    (∀ i, IsPoint (π.elem i) →
      ϕ '' (Subtype.val '' π.elem i) ∈ vertices)

end Subdivisions

namespace Subdivision

variable {M : Type*} [TopologicalSpace M]

/-- all the vertices, edges and faces of a subdivision -/
def elements (S : Subdivision M) : Set (Set M) :=
  S.vertices ∪ S.edges ∪ S.faces

end subdivision

end GuibasStolfi
