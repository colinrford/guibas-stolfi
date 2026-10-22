module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Use

@[expose] public section

open Set Filter Topology

namespace GuibasStolfi

variable {M : Type*} [TopologicalSpace M]

/-! ## Separation and Incidence -/
section Separation

/-- Separable subsets: Two sets are separable if they have disjoint nbhds -/
def Separable (A B : Set M) : Prop :=
  ∃ U ∈ 𝓝ˢ A, ∃ V ∈ 𝓝ˢ B, Disjoint U V

/-- Incident subsets -/
def Incident (A B : Set M) : Prop :=
  ¬Separable A B

/-- Symmetry of separable definition -/
lemma Separable.symm {A B : Set M}
    (h : Separable A B) : Separable B A := by
  unfold Separable at h ⊢
  obtain ⟨U, hU, V, hV, hUV⟩ := h
  use V, hV, U, hU
  exact hUV.symm

/-- Symmetry of incident definition -/
lemma Incident.symm {A B : Set M}
    (h : Incident A B) : Incident B A := by
  unfold Incident at h ⊢
  intro hBA
  exact h hBA.symm

end Separation

/-! ## Shapes: points, lines, disks -/
section Shapes

/-- Point -/
def IsPoint (s : Set M) : Prop :=
  ∃ p, s = {p}

/-- Line homeomorphic to open interval of ℝ -/
def IsLine (s : Set M) : Prop :=
  Nonempty (s ≃ₜ Set.Ioo (0 : ℝ) 1)

abbrev Plane := ℂ

/-- Disk is (subset homeomorphic to) open unit ball -/
def IsDisk (s : Set M) : Prop :=
  Nonempty (s ≃ₜ Metric.ball (0 : Plane) 1)

/-- the interval is not a singleton -/
lemma not_subsingleton_Ioo :
    ¬ Subsingleton (Set.Ioo (0 : ℝ) 1) := by
  intro h
  let a : Set.Ioo (0 : ℝ) 1 :=
    ⟨1 / 4, by norm_num, by norm_num⟩
  let b : Set.Ioo (0 : ℝ) 1 :=
    ⟨1 / 2, by norm_num, by norm_num⟩
  have hab : a = b := h.elim a b
  have hvalues : (1 / 4 : ℝ) = 1 / 2 :=
    congrArg Subtype.val hab
  norm_num at hvalues

/-- the ball is not a singleton neither -/
lemma not_subsingleton_ball :
    ¬ Subsingleton (Metric.ball (0 : Plane) 1) := by
  intro h
  let a : Metric.ball (0 : Plane) 1 :=
    ⟨0, by norm_num [Metric.mem_ball]⟩
  let b : Metric.ball (0 : Plane) 1 :=
    ⟨1 / 2, by norm_num [Metric.mem_ball]⟩
  have hab : a = b := h.elim a b
  have hvalues : (0 : Plane) = (1 / 2 : Plane) :=
    congrArg Subtype.val hab
  norm_num at hvalues

lemma shapes_not_homeomorphic :
    (∀ A B : Set M, IsPoint A → IsLine B → IsEmpty (A ≃ₜ B)) ∧
    (∀ A B : Set M, IsPoint A → IsDisk B → IsEmpty (A ≃ₜ B)) ∧
    (∀ A B : Set M, IsLine A → IsDisk B → IsEmpty (A ≃ₜ B)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hA hB
    obtain ⟨p, hp⟩ := hA
    subst A
    constructor
    intro f
    obtain ⟨g⟩ := hB
    let e := f.trans g
    have hsingle : Subsingleton (Set.Ioo (0 : ℝ) 1) :=
      e.symm.toEquiv.subsingleton
    exact not_subsingleton_Ioo hsingle
  · intro A B hA hB
    obtain ⟨p, hp⟩ := hA
    subst A
    constructor
    intro f
    obtain ⟨g⟩ := hB
    let e := f.trans g
    have hsingle : Subsingleton (Metric.ball (0 : Plane) 1) :=
      e.symm.toEquiv.subsingleton
    exact not_subsingleton_ball hsingle
  · intro A B hA hB
    constructor
    intro f
    obtain ⟨l⟩ := hA
    obtain ⟨d⟩ := hB
    let e := l.symm.trans (f.trans d)
    let g : Plane ≃ₜ Set.Ioo (0 : ℝ) 1 :=
      Homeomorph.unitBall.trans e.symm
    let q : Plane :=
      g.symm ⟨1 / 2, by norm_num, by norm_num⟩
    have hrank : 1 < Module.rank ℝ Plane := by
      rw [Complex.rank_real_complex]
      norm_num
    have hconnected : IsConnected ({q}ᶜ : Set Plane) :=
      isConnected_compl_singleton_of_one_lt_rank hrank q
    have himage : IsConnected (g '' ({q}ᶜ : Set Plane)) :=
      hconnected.image g g.continuous.continuousOn
    let S : Set ℝ :=
      Subtype.val '' (g '' ({q}ᶜ : Set Plane))
    have hS : IsPreconnected S :=
      himage.isPreconnected.image Subtype.val
        continuous_subtype_val.continuousOn
    have mem : ∀ (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1),
        y ≠ 1 / 2 → y ∈ S := by
      intro y hy hne
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      refine ⟨g.symm ⟨y, hy⟩, ?_, by simp⟩
      intro heq
      apply hne
      simpa [q] using
        congrArg Subtype.val (g.symm.injective heq)
    have hquarter : (1 / 4 : ℝ) ∈ S :=
      mem (1 / 4) ⟨by norm_num, by norm_num⟩ (by norm_num)
    have hthreequarters : (3 / 4 : ℝ) ∈ S :=
      mem (3 / 4) ⟨by norm_num, by norm_num⟩ (by norm_num)
    have hhalf : (1 / 2 : ℝ) ∈ S :=
      hS.Icc_subset hquarter hthreequarters
        ⟨by norm_num, by norm_num⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hvalue⟩ := hhalf
    exact hx (g.injective (Subtype.ext (by
      simpa [q] using hvalue)))

end Shapes

/-! ## Two-dim manifolds -/
section Manifolds

/-- def of 2-manifold. -/
def IsTwoManifold (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ x : M, ∃ U : Set M, x ∈ U ∧ IsOpen U ∧ IsDisk U

end Manifolds

end GuibasStolfi
