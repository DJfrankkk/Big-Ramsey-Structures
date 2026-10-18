import RelationalRamsey632.Milliken.DimensionTransport
import Generic3Ramsey.SourceColoredForests

namespace RelationalRamsey632.Milliken

open Filter
open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

def HalpernLauchliDimension (d : ℕ) : Prop :=
  ∀ (α : Fin d → Type) [∀ i, DecidableEq (α i)]
    (R : ∀ i, α i → α i → Prop)
    (T : ∀ i, FiniteLevelTree (α i) (R i))
    (K : Type) [Fintype K], StrongSubtreeRamsey T K

theorem halpernLauchli_zero : HalpernLauchliDimension 0 := by
  intro α _ R T K _ c
  let x0 : VectorNode T := fun i => Fin.elim0 i
  refine ⟨⟨id, strictMono_id, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), c x0, ?_⟩⟩
  intro n x _
  have hx : x = x0 := funext (fun i => Fin.elim0 i)
  exact congrArg c hx

variable {α : Type} [DecidableEq α] {R : α → α → Prop} (T : FiniteLevelTree α R)

noncomputable def ambientSingleColor {K : Type} (c : T.TreeNode → K) (u : α) : K := by
  classical
  exact if hu : ∃ n, u ∈ T.nodes n then c ⟨u, hu⟩ else c T.rootNode

theorem ambientSingleColor_node {K : Type} (c : T.TreeNode → K) (u : T.TreeNode) :
    ambientSingleColor T c u.val = c u := by
  simp only [ambientSingleColor, dif_pos u.property]
  exact congrArg c (Subtype.ext rfl)

/-- The one-coordinate strong theorem is assembled from the already
verified ultrafilter colored-forest recursion. -/
theorem one_tree_strong {K : Type} [Fintype K] (c : T.TreeNode → K) :
    ∃ F : T.StrongFrame, ∃ color : K,
      ∀ n (u : T.TreeNode), u.val ∈ F.nodes n → c u = color := by
  classical
  let color := ambientSingleColor T c
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨D, _⟩ := T.colorRoots_above (I := Unit) color U hU (fun _ => T.rootNode)
  obtain ⟨initial, _, hinit⟩ := D.initial_stage_exists hU 0
  obtain ⟨root, hroot⟩ := hinit ()
  let stages := D.stages initial hU
  let F : T.StrongFrame := {
    index := fun n => (stages n).index
    index_strictMono := D.stages_index_strictMono initial hU
    nodes := fun n => ((stages n).nodes ()).image Subtype.val
    root := root.val
    nodes_zero := by
      change (initial.nodes ()).image (Subtype.val : T.TreeNode → α) = {root.val}
      rw [hroot]
      exact Finset.image_singleton (Subtype.val : T.TreeNode → α) root
    nodes_subset := by
      intro n u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact (stages n).height () v hv ▸ T.nodeHeight_mem v
    parent := by
      intro n w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨u, hu, q, hq, hqv⟩ := D.stages_parent initial hU n () v hv
      exact ⟨u.val, Finset.mem_image.mpr ⟨u, hu, rfl⟩,
        T.rel_trans (Finset.mem_filter.mp hq).2 hqv⟩
    successor := by
      intro n u hu v hv huv
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
      let v' : T.TreeNode := ⟨v, (stages n).index + 1, hv⟩
      have hv' : v' ∈ (stages n).children p :=
        Finset.mem_filter.mpr ⟨(T.mem_levelNodes _ _).mpr hv, hpu.symm ▸ huv⟩
      obtain ⟨w, hw, huniq⟩ := D.stages_successor initial hU n () p hp v' hv'
      refine ⟨w.val, ⟨Finset.mem_image.mpr ⟨w, hw.1, rfl⟩, hw.2⟩, ?_⟩
      intro q hq
      obtain ⟨q', hq', heq⟩ := Finset.mem_image.mp hq.1
      have hqq' : R v'.val q'.val := heq.symm ▸ hq.2
      exact heq.symm.trans (congrArg Subtype.val (huniq q' ⟨hq', hqq'⟩)) }
  refine ⟨F, D.color (), ?_⟩
  intro n u hu
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hu
  have hvu : v = u := Subtype.ext heq
  have hc := (stages n).colored () v hv
  rw [show color v.val = c v from ambientSingleColor_node T c v] at hc
  exact hvu ▸ hc

theorem halpernLauchli_one : HalpernLauchliDimension 1 := by
  classical
  intro α _ R T K _ c
  let tuple : (T 0).TreeNode → VectorNode T := fun u i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact u
  obtain ⟨F, color, hcolor⟩ := one_tree_strong (T 0) (c ∘ tuple)
  let frames : ∀ i, (T i).StrongFrame := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact F
  have hindex : ∀ i, (frames i).index = F.index := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  refine ⟨⟨F.index, F.index_strictMono, frames, hindex, color, ?_⟩⟩
  intro n x hx
  have htuple : tuple (x 0) = x := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hc := hcolor n (x 0) (hx 0)
  change c (tuple (x 0)) = color at hc
  exact htuple ▸ hc

end RelationalRamsey632.Milliken
