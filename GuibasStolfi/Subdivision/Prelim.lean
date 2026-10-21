module

public import Mathlib

@[expose] public section

open Set Filter Topology

namespace GuibasStolfi

variable {M : Type*} [TopologicalSpace M]

/-- Separable subsets: Two disjoint sets have disjoint nbhds -/
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

end GuibasStolfi
