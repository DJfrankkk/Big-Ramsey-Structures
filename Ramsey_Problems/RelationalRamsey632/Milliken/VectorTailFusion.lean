import RelationalRamsey632.Milliken.LevelSelection

/-!
# Finite-frontier forest stabilization in the same vector dimension

Each obligation selects exactly one cone in each coordinate. SS is applied
only to that d-coordinate tuple. Other cones are completed on the resulting
common level set. Earlier homogeneous tuples survive by actual subtree
inclusion. No higher-dimensional simultaneous SS principle is used.
-/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop}
    {B : I → Type} [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (T : ∀ i, B i → FiniteLevelTree (α i) (R i))

abbrev ConeTuple := ∀ i, B i

structure StrongForest where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  frames : ∀ i b, (T i b).StrongFrame
  frame_index : ∀ i b, (frames i b).index = index

namespace StrongForest

variable {T} (F : StrongForest T) {K : Type}

def Homogeneous (p : ConeTuple (B := B)) (c : (∀ i, α i) → K) : Prop :=
  ∃ color, ∀ n x, (∀ i, x i ∈ (F.frames i (p i)).nodes n) → c x = color

structure Refinement where
  forest : StrongForest T
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  index_eq : forest.index = F.index ∘ selector
  subset : ∀ i b n, (forest.frames i b).nodes n ⊆ (F.frames i b).nodes (selector n)

namespace Refinement

variable {F} (G : F.Refinement)

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)] in
theorem preserves {p : ConeTuple (B := B)} {c : (∀ i, α i) → K}
    (h : F.Homogeneous p c) : G.forest.Homogeneous p c := by
  obtain ⟨color, hc⟩ := h
  exact ⟨color, fun n x hx => hc (G.selector n) x (fun i => G.subset i (p i) n (hx i))⟩

noncomputable def trans (H : G.forest.Refinement) : F.Refinement where
  forest := H.forest
  selector := G.selector ∘ H.selector
  selector_strictMono := G.selector_strictMono.comp H.selector_strictMono
  index_eq := by rw [H.index_eq, G.index_eq]; rfl
  subset i b n := (H.subset i b n).trans (G.subset i b (H.selector n))

end Refinement

noncomputable def identityRefinement : F.Refinement where
  forest := F
  selector := id
  selector_strictMono := strictMono_id
  index_eq := rfl
  subset _ _ _ := Finset.Subset.refl _

variable (p : ConeTuple (B := B)) (c : (∀ i, α i) → K)

abbrev selectedTrees := fun i => (F.frames i (p i)).toTree

def selectedColor : VectorNode (F.selectedTrees p) → K :=
  fun x => c (fun i => (x i).val)

noncomputable def completion (H : HomogeneousStrongVector (F.selectedTrees p) (F.selectedColor p c))
    (i : I) (b : B i) : (F.frames i b).toTree.StrongFrame := by
  classical
  by_cases hb : b = p i
  · subst b
    exact H.frames i
  · exact LevelSelection.frame (F.frames i b).toTree H.index H.index_strictMono

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (B i)] in
theorem completion_index (H : HomogeneousStrongVector (F.selectedTrees p) (F.selectedColor p c))
    (i : I) (b : B i) :
    (F.completion p c H i b).index = H.index := by
  classical
  by_cases hb : b = p i
  · subst b
    simpa [completion] using H.frame_index i
  · simp only [completion, dif_neg hb, LevelSelection.frame_index]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (B i)] in
theorem completion_selected (H : HomogeneousStrongVector (F.selectedTrees p) (F.selectedColor p c))
    (i : I) : F.completion p c H i (p i) = H.frames i := by
  classical
  simp [completion]

noncomputable def step (H : HomogeneousStrongVector (F.selectedTrees p) (F.selectedColor p c)) :
    F.Refinement where
  forest := {
    index := F.index ∘ H.index
    index_strictMono := F.index_strictMono.comp H.index_strictMono
    frames i b := (F.frames i b).comp (F.completion p c H i b)
    frame_index i b := by
      funext n
      change (F.frames i b).index ((F.completion p c H i b).index n) =
        F.index (H.index n)
      rw [F.frame_index, F.completion_index]
  }
  selector := H.index
  selector_strictMono := H.index_strictMono
  index_eq := rfl
  subset i b n := by
    have hh := (F.completion p c H i b).nodes_subset n
    rw [F.completion_index] at hh
    exact hh

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (B i)] in
theorem step_homogeneous (H : HomogeneousStrongVector (F.selectedTrees p) (F.selectedColor p c)) :
    (F.step p c H).forest.Homogeneous p c := by
  refine ⟨H.color, ?_⟩
  intro n x hx
  have hx' : ∀ i, x i ∈ (H.frames i).nodes n := by
    intro i
    have hi := hx i
    change x i ∈ (F.completion p c H i (p i)).nodes n at hi
    rwa [F.completion_selected] at hi
  let y : VectorNode (F.selectedTrees p) := fun i =>
    ⟨x i, (H.frames i).index n, (H.frames i).nodes_subset n (hx' i)⟩
  exact H.colored n y hx'

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (B i)] in
theorem step_exists
    (hSS : StrongSubtreeRamsey (F.selectedTrees p) K) :
    ∃ G : F.Refinement, G.forest.Homogeneous p c := by
  obtain ⟨H⟩ := hSS (F.selectedColor p c)
  exact ⟨F.step p c H, F.step_homogeneous p c H⟩

end StrongForest

/-- The same d-coordinate SS theorem is reapplied to actual strong cone
trees. This uniformity is needed by the dimensional induction. -/
def SameDimensionSS (K : Type) : Prop :=
  ∀ S : ∀ i, FiniteLevelTree (α i) (R i), StrongSubtreeRamsey S K

omit [DecidableEq I] [∀ i, Fintype (B i)] in
theorem finite_frontier_stabilization {K : Type}
    (hSS : SameDimensionSS (α := α) (R := R) K)
    (F : StrongForest T) (c : (∀ i, α i) → K)
    (obligations : Finset (ConeTuple (B := B))) :
    ∃ G : F.Refinement, ∀ p ∈ obligations, G.forest.Homogeneous p c := by
  classical
  induction obligations using Finset.induction_on with
  | empty => exact ⟨F.identityRefinement, by simp⟩
  | @insert p obligations hp ih =>
    obtain ⟨G, hG⟩ := ih
    obtain ⟨H, hH⟩ := G.forest.step_exists p c (hSS (G.forest.selectedTrees p))
    refine ⟨G.trans H, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hH
    · exact H.preserves (hG q hq)

/- Every tuple of a fixed finite frontier can be stabilized, while keeping
the vector dimension I unchanged throughout the construction. -/
omit [DecidableEq I] in
theorem all_frontier_stabilization {K : Type}
    (hSS : SameDimensionSS (α := α) (R := R) K)
    (F : StrongForest T) (c : (∀ i, α i) → K) :
    ∃ G : F.Refinement, ∀ p : ConeTuple (B := B), G.forest.Homogeneous p c := by
  classical
  obtain ⟨G, hG⟩ := finite_frontier_stabilization T hSS F c Finset.univ
  exact ⟨G, fun p => hG p (Finset.mem_univ p)⟩

end RelationalRamsey632.Milliken
