module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.Choose
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas

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

/-- if A meets the closure of B, then A and B are incident -/
lemma incident_of_mem_closure {A B : Set M}
    (h : (A ∩ closure B).Nonempty) : 
    Incident A B := by
  unfold Incident
  intro hsep
  obtain ⟨U, hU, V, hV, hUV⟩ := hsep
  obtain ⟨x, hxA, hxB⟩ := h
  have hUx : U ∈ 𝓝 x :=
    mem_nhdsSet_iff_forall.mp hU x hxA
  obtain ⟨y, hyU, hyB⟩ :=
    mem_closure_iff_nhds.mp hxB U hUx
  have hyV : y ∈ V :=
    subset_of_mem_nhdsSet hV hyB
  exact hUV.ne_of_mem hyU hyV rfl

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

/-- There is no continuous injection from the plane into the real line. -/
lemma not_injective_of_continuous_plane_real
    {f : Plane → ℝ} (hf : Continuous f) :
    ¬ Function.Injective f := by
  intro hinj
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [Complex.rank_real_complex]
    norm_num
  obtain ⟨a, b, hab⟩ := exists_pair_ne Plane
  wlog h : f a < f b generalizing a b
  · exact this b a hab.symm
      ((lt_or_gt_of_ne (hinj.ne hab)).resolve_left h)
  obtain ⟨q, hq⟩ :
      (f a + f b) / 2 ∈ Set.range f :=
    (isPreconnected_range hf).Icc_subset
      ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨by linarith, by linarith⟩
  have hS :=
    (isConnected_compl_singleton_of_one_lt_rank hrank q).isPreconnected.image
      f hf.continuousOn
  have ha : a ≠ q := by
    rintro rfl
    linarith
  have hb : b ≠ q := by
    rintro rfl
    linarith
  obtain ⟨y, hy, hyq⟩ := hS.Icc_subset
    ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    (show (f a + f b) / 2 ∈ Set.Icc (f a) (f b) from
      ⟨by linarith, by linarith⟩)
  exact hy (hinj (hyq.trans hq.symm))

/-- A point or line is a countable union of compact sets. -/
private lemma exists_compact_cover
    {s : Set M} (hs : IsPoint s ∨ IsLine s) :
    ∃ K : ℕ → Set M,
      (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s := by
  rcases hs with hp | hl
  · obtain ⟨p, rfl⟩ := hp
    exact ⟨fun _ => {p}, fun _ => isCompact_singleton,
      Set.iUnion_const _⟩
  · obtain ⟨f⟩ := hl
    let I : ℕ → Set ℝ :=
      fun n => Set.Icc (1 / (n + 2)) (1 - 1 / (n + 2))
    have hI : ∀ n, I n ⊆ Set.Ioo 0 1 := by
      intro n x hx
      have hpos : (0 : ℝ) < 1 / (n + 2) := by positivity
      exact ⟨hpos.trans_le hx.1,
        hx.2.trans_lt (by linarith)⟩
    refine ⟨fun n =>
      Subtype.val '' (f.symm '' (Subtype.val ⁻¹' I n)), ?_, ?_⟩
    · intro n
      have hc :
          IsCompact (Subtype.val ⁻¹' I n : Set (Set.Ioo (0 : ℝ) 1)) := by
        rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range,
          Subtype.range_coe, Set.inter_eq_left.mpr (hI n)]
        exact isCompact_Icc
      exact (hc.image f.symm.continuous).image continuous_subtype_val
    · ext x
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨n, y, ⟨t, _, rfl⟩, rfl⟩
        exact (f.symm t).property
      · intro hx
        obtain ⟨⟨t, ht0, ht1⟩, hft⟩ :
            ∃ t, f.symm t = ⟨x, hx⟩ :=
          ⟨f ⟨x, hx⟩, by simp⟩
        obtain ⟨n, hn⟩ :=
          exists_nat_one_div_lt (lt_min ht0 (sub_pos.mpr ht1))
        have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / (n + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        refine ⟨n, ⟨x, hx⟩,
          ⟨⟨t, ht0, ht1⟩, ⟨?_, ?_⟩, hft⟩, rfl⟩
        · linarith [min_le_left t (1 - t)]
        · linarith [min_le_right t (1 - t)]

/-- A disk cannot be covered by finitely many points and lines
in a Hausdorff space. -/
lemma not_disk_subset_finite_union [T2Space M]
    {D : Set M} (hD : IsDisk D)
    {C : Set (Set M)}
    (hC : C.Finite)
    (hC' : ∀ s ∈ C, IsPoint s ∨ IsLine s) :
    ¬ D ⊆ ⋃₀ C := by
  intro hDC
  choose! K hKc hKs using
    fun s hs => exists_compact_cover (hC' s hs)
  obtain ⟨g⟩ := hD
  let ψ : Plane ≃ₜ D := Homeomorph.unitBall.trans g.symm
  have := hC.to_subtype
  let A : C × ℕ → Set Plane :=
    fun i => (Subtype.val ∘ ψ) ⁻¹' K i.1 i.2
  have hAc : ∀ i, IsClosed (A i) := fun i =>
    (hKc i.1 i.1.property i.2).isClosed.preimage
      (continuous_subtype_val.comp ψ.continuous)
  have hAu : ⋃ i, A i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨s, hs, hxs⟩ := hDC (ψ x).property
    rw [← hKs s hs] at hxs
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxs
    exact Set.mem_iUnion.mpr ⟨(⟨s, hs⟩, n), hn⟩
  obtain ⟨⟨⟨s, hs⟩, n⟩, c, hc⟩ :=
    nonempty_interior_of_iUnion_of_closed hAc hAu
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior c hc
  let β := OpenPartialHomeomorph.univBall c r
  have hβc : Continuous β :=
    continuousOn_univ.mp (by simpa [β] using β.continuousOn)
  have hβi : Function.Injective β := fun x y h =>
    β.injOn (by simp [β]) (by simp [β]) h
  have hβb : ∀ x, β x ∈ Metric.ball c r := fun x =>
    OpenPartialHomeomorph.univBall_target c hr ▸
      β.map_source (by simp [β])
  let Φ : Plane → M := fun x => (ψ (β x) : M)
  have hΦc : Continuous Φ :=
    continuous_subtype_val.comp (ψ.continuous.comp hβc)
  have hΦi : Function.Injective Φ :=
    Subtype.val_injective.comp (ψ.injective.comp hβi)
  have hΦs : ∀ x, Φ x ∈ s := fun x =>
    hKs s hs ▸ Set.mem_iUnion.mpr
      ⟨n, interior_subset (s := A (⟨s, hs⟩, n))
        (hball (hβb x))⟩
  rcases hC' s hs with hp | hl
  · obtain ⟨p, rfl⟩ := hp
    obtain ⟨a, b, hab⟩ := exists_pair_ne Plane
    exact hab (hΦi ((hΦs a).trans (hΦs b).symm))
  · obtain ⟨f⟩ := hl
    refine not_injective_of_continuous_plane_real
      (f := fun x => (f ⟨Φ x, hΦs x⟩ : ℝ))
      (continuous_subtype_val.comp
        (f.continuous.comp (hΦc.subtype_mk hΦs))) ?_
    intro x y h
    exact hΦi (Subtype.mk.inj (f.injective (Subtype.ext h)))

end Shapes

/-! ## Two-dim manifolds -/
section Manifolds

/-- def of 2-manifold. -/
def IsTwoManifold (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ x : M, ∃ U : Set M, x ∈ U ∧ IsOpen U ∧ IsDisk U

/-- Every open neighborhood in a 2-manifold contains
an open disk neighborhood of the same point. -/
lemma IsTwoManifold.exists_disk_subset
    {M : Type*} [TopologicalSpace M]
    (hM : IsTwoManifold M)
    {W : Set M} (hW : IsOpen W)
    {x : M} (hx : x ∈ W) :
    ∃ D ⊆ W, IsOpen D ∧ x ∈ D ∧ IsDisk D := by
  obtain ⟨U, hxU, hU, ⟨f⟩⟩ := hM x
  let ψ : Plane ≃ₜ U := Homeomorph.unitBall.trans f.symm
  let j : Plane → M := Subtype.val ∘ ψ
  have hj : Topology.IsOpenEmbedding j :=
    hU.isOpenEmbedding_subtypeVal.comp ψ.isOpenEmbedding
  let c : Plane := ψ.symm ⟨x, hxU⟩
  have hjc : j c = x := by
    simp [j, c]
  have hc : c ∈ j ⁻¹' W := by
    simpa [Set.mem_preimage, hjc] using hx
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (hW.preimage hj.continuous) c hc
  refine ⟨j '' Metric.ball c r, ?_,
    hj.isOpenMap _ Metric.isOpen_ball, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hball hz
  · exact ⟨c, Metric.mem_ball_self hr, hjc⟩
  · let b : Metric.ball (0 : Plane) 1 ≃ₜ Metric.ball c r :=
      (OpenPartialHomeomorph.unitBallBall c r hr).toHomeomorphSourceTarget
    exact ⟨(hj.isEmbedding.homeomorphImage
      (Metric.ball c r)).symm.trans b.symm⟩

end Manifolds

end GuibasStolfi
