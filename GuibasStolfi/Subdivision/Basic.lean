module

public import GuibasStolfi.Subdivision.Prelim
public import Mathlib.Order.Setoid.Partition
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.LinearCombination

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

namespace SimplePath

variable (π : SimplePath)

/-- pieces with distinct indices are disjoint -/
lemma disjoint_elem {j k : Fin (π.m + 1)} (h : j ≠ k) :
    Disjoint (π.elem j) (π.elem k) := by
  have hpieces : π.elem j ≠ π.elem k :=
    π.injective.ne h
  exact π.isPartition.pairwiseDisjoint
    (Set.mem_range_self j) (Set.mem_range_self k) hpieces

/-- every piece of boundary partition is nonempty -/
lemma elem_nonempty (j : Fin (π.m + 1)) :
    (π.elem j).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro hempty
  have hmem : π.elem j ∈ Set.range π.elem :=
    Set.mem_range_self j
  rw [hempty] at hmem
  exact π.isPartition.1 hmem

/-- every point of the circle belongs to a boundary piece -/
lemma exists_mem_elem (x : UnitCircle) :
    ∃ j, x ∈ π.elem j := by
  obtain ⟨P, hP, _⟩ := π.isPartition.2 x
  obtain ⟨hPrange, hxP⟩ := hP
  obtain ⟨j, hj⟩ := hPrange
  use j
  rw [hj]
  exact hxP

/-- a distinct piece connected to an open arc is a point in its closure -/
lemma exists_eq_singleton_mem_closure
    {i k : Fin (π.m + 1)}
    (hi : IsOpen (π.elem i))
    (hki : k ≠ i)
    (hc : IsPreconnected (π.elem k ∪ π.elem i)) :
    ∃ a, π.elem k = {a} ∧ a ∈ closure (π.elem i) := by
  obtain ⟨z, hz⟩ := π.elem_nonempty i
  rcases π.isPoint_or_arc k with hpoint | ⟨hk, hline⟩
  · obtain ⟨a, ha⟩ := hpoint
    refine ⟨a, ha, ?_⟩
    by_contra hac
    obtain ⟨y, _, hyOutside, hyArc⟩ :=
      hc _ _ isClosed_closure.isOpen_compl hi
        (fun y hy => (ha ▸ hy).elim
          (fun hy => Or.inl (Set.mem_singleton_iff.1 hy ▸ hac))
          Or.inr)
        ⟨a, Or.inl (ha ▸ rfl), hac⟩
        ⟨z, Or.inr hz, hz⟩
    exact hyOutside (subset_closure hyArc)
  · exfalso
    obtain ⟨w, hw⟩ := π.elem_nonempty k
    obtain ⟨y, _, hyK, hyI⟩ :=
      hc _ _ hk hi
        (fun _ => id)
        ⟨w, Or.inl hw, hw⟩
        ⟨z, Or.inr hz, hz⟩
    exact (π.disjoint_elem hki).notMem_of_mem_left hyK hyI

/-- piece following an arc is a point, provided its index is distinct -/
lemma next_isPoint (i : Fin (π.m + 1))
    (hi : IsOpen (π.elem i) ∧ IsLine (π.elem i))
    (hne : i + 1 ≠ i) :
    IsPoint (π.elem (i + 1)) := by
  have hc : IsPreconnected (π.elem (i + 1) ∪ π.elem i) := by
    simpa [Set.union_comm] using (π.adjacent i).isPreconnected
  obtain ⟨a, ha, _⟩ :=
    π.exists_eq_singleton_mem_closure hi.1 hne hc
  exact ⟨a, ha⟩

/-- piece preceding arc is a point, provided its index is distinct -/
lemma prev_isPoint (i : Fin (π.m + 1))
    (hi : IsOpen (π.elem i) ∧ IsLine (π.elem i))
    (hne : i - 1 ≠ i) :
    IsPoint (π.elem (i - 1)) := by
  have hc : IsPreconnected (π.elem (i - 1) ∪ π.elem i) := by
    simpa [Set.union_comm] using (π.adjacent (i - 1)).isPreconnected
  obtain ⟨a, ha, _⟩ :=
    π.exists_eq_singleton_mem_closure hi.1 hne hc
  exact ⟨a, ha⟩

/-- an arc and its neighbors lie in the arc's closure -/
lemma neighbors_subset_closure (i : Fin (π.m + 1))
    (hi : IsOpen (π.elem i) ∧ IsLine (π.elem i)) :
    π.elem (i - 1) ∪ π.elem i ∪ π.elem (i + 1) ⊆
      closure (π.elem i) := by
  refine Set.union_subset
    (Set.union_subset ?_ subset_closure) ?_
  · by_cases h : i - 1 = i
    · rw [h]
      exact subset_closure
    · obtain ⟨a, ha, hac⟩ :=
        π.exists_eq_singleton_mem_closure hi.1 h
          (by simpa using (π.adjacent (i - 1)).isPreconnected)
      rw [ha]
      exact Set.singleton_subset_iff.mpr hac
  · by_cases h : i + 1 = i
    · rw [h]
      exact subset_closure
    · obtain ⟨a, ha, hac⟩ :=
        π.exists_eq_singleton_mem_closure hi.1 h
          (by simpa [Set.union_comm] using
            (π.adjacent i).isPreconnected)
      rw [ha]
      exact Set.singleton_subset_iff.mpr hac

/-- every arc piece is preconnected -/
lemma isPreconnected_elem (i : Fin (π.m + 1))
    (hi : IsLine (π.elem i)) :
    IsPreconnected (π.elem i) := by
  obtain ⟨e⟩ := hi
  have : PreconnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hrange :
      Set.range (Subtype.val ∘ e.symm) = π.elem i := by
    rw [Set.range_comp, e.symm.surjective.range_eq,
      Set.image_univ, Subtype.range_coe]
  rw [← hrange]
  exact isPreconnected_range
    (continuous_subtype_val.comp e.symm.continuous)

end SimplePath

/-- preconnected subset of circle gains at most two closure points -/
lemma closure_subset_of_isPreconnected
    {s : Set UnitCircle} (hs : IsPreconnected s) :
    ∃ u v : UnitCircle, closure s ⊆ s ∪ {u, v} := by
  by_cases houtside : ∃ a : UnitCircle, a ∉ s
  · obtain ⟨a, ha⟩ := houtside
    rcases s.eq_empty_or_nonempty with hempty | hnonempty
    · subst s
      exact ⟨a, a, by simp⟩
    · have : Fact (0 < 2 * Real.pi) :=
        ⟨mul_pos (by norm_num) Real.pi_pos⟩
      let e : UnitCircle ≃ₜ AddCircle (2 * Real.pi) :=
        (Homeomorph.refl UnitCircle : UnitCircle ≃ₜ Circle).trans
          AddCircle.homeomorphCircle'.symm
      obtain ⟨t₀, ht₀⟩ :
          ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = e a :=
        QuotientAddGroup.mk_surjective (e a)
      let φ := AddCircle.openPartialHomeomorphCoe (2 * Real.pi) t₀
      have hsT : e '' s ⊆ φ.target := by
        intro y hy
        change y ≠ (t₀ : AddCircle (2 * Real.pi))
        intro hycut
        obtain ⟨x, hxs, hxy⟩ := hy
        have hxa : x = a :=
          e.injective (hxy.trans (hycut.trans ht₀))
        exact ha (hxa ▸ hxs)
      let P : Set ℝ := φ.symm '' (e '' s)
      have hPI : P ⊆ Set.Ioo t₀ (t₀ + 2 * Real.pi) := by
        rintro _ ⟨y, hy, rfl⟩
        exact φ.map_target (hsT hy)
      have hP : IsConnected P := by
        refine ⟨(hnonempty.image e).image φ.symm, ?_⟩
        exact (hs.image e e.continuous.continuousOn).image
          φ.symm (φ.continuousOn_symm.mono hsT)
      have hbelow : BddBelow P :=
        ⟨t₀, fun _ hx => (hPI hx).1.le⟩
      have habove : BddAbove P :=
        ⟨t₀ + 2 * Real.pi, fun _ hx => (hPI hx).2.le⟩
      have hPs :
          ((↑) : ℝ → AddCircle (2 * Real.pi)) '' P = e '' s := by
        dsimp only [P]
        rw [Set.image_image]
        exact (Set.image_congr fun x hx =>
          φ.right_inv (hsT hx)).trans (Set.image_id _)
      have hcl :
          closure (e '' s) ⊆
            ((↑) : ℝ → AddCircle (2 * Real.pi)) ''
              Set.Icc (sInf P) (sSup P) := by
        rw [← hPs]
        exact closure_minimal
          (Set.image_mono
            (subset_Icc_csInf_csSup hbelow habove))
          ((isCompact_Icc.image
            (AddCircle.continuous_mk' (2 * Real.pi))).isClosed)
      have hboundary :
          closure (e '' s) ⊆
            e '' s ∪
              {((sInf P : ℝ) : AddCircle (2 * Real.pi)),
               ((sSup P : ℝ) : AddCircle (2 * Real.pi))} := by
        intro y hy
        obtain ⟨t, ⟨hlo, hhi⟩, rfl⟩ := hcl hy
        rcases hlo.eq_or_lt with rfl | hlo
        · exact Or.inr (Or.inl rfl)
        rcases hhi.eq_or_lt with rfl | hhi
        · exact Or.inr (Or.inr rfl)
        exact Or.inl (hPs ▸ Set.mem_image_of_mem _
          (hP.Ioo_csInf_csSup_subset hbelow habove ⟨hlo, hhi⟩))
      refine ⟨e.symm (sInf P : ℝ), e.symm (sSup P : ℝ), ?_⟩
      intro x hx
      have hex : e x ∈ closure (e '' s) :=
        e.image_closure s ▸ Set.mem_image_of_mem e hx
      rcases hboundary hex with himage | hendpoints
      · obtain ⟨y, hy, hyx⟩ := himage
        exact Or.inl (e.injective hyx ▸ hy)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hendpoints
        rcases hendpoints with heq | heq
        · exact Or.inr (Or.inl
            ((e.symm_apply_apply x).symm.trans
              (congrArg e.symm heq)))
        · exact Or.inr (Or.inr
            ((e.symm_apply_apply x).symm.trans
              (congrArg e.symm heq)))
  · push Not at houtside
    let u : UnitCircle := ⟨1, by norm_num [Metric.mem_sphere]⟩
    exact ⟨u, u, fun x _ => Or.inl (houtside x)⟩

/-- If the preceding and following indices coincide, there is no third index distinct from both. -/
private lemma Fin.false_of_sub_one_eq_add_one
    {n : ℕ} {i j : Fin (n + 1)}
    (h : i - 1 = i + 1)
    (hji : j ≠ i)
    (hji' : j ≠ i - 1) : False := by
  rcases n with _ | _ | n
  · exact hji (Fin.ext (by
      have := i.2
      have := j.2
      omega))
  · revert i j
    decide
  · open Fin.CommRing in
    have h2 : (2 : Fin (n + 3)) = 0 := by
      linear_combination (-1 : Fin (n + 3)) * h
    rw [Fin.ext_iff] at h2
    simp at h2
    rw [Nat.mod_eq_of_lt (by omega)] at h2
    omega

namespace SimplePath

variable (π : SimplePath)

/-- closure of an arc consists of the arc and its neighboring pieces. -/
lemma alternate (i : Fin (π.m + 1))
    (hi : IsOpen (π.elem i) ∧ IsLine (π.elem i)) :
    closure (π.elem i) =
      π.elem (i - 1) ∪ π.elem i ∪ π.elem (i + 1) := by
  sorry

end SimplePath

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

end Subdivision

end GuibasStolfi
