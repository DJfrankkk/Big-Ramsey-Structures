import RelationalRamsey632.Milliken.HalpernLauchliInduction
import RelationalRamsey632.Milliken.VectorSectionFusion

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [Nonempty I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    {β : Type} [DecidableEq β] {Q : β → β → Prop} (B : FiniteLevelTree β Q)

noncomputable def ambientVectorLastColor {K : Type}
    (c : VectorNode T → B.TreeNode → K) (x : ∀ i, α i) (y : β) : K := by
  classical
  let default := c (fun i => (T i).rootNode) B.rootNode
  exact if hx : ∀ i, ∃ n, x i ∈ (T i).nodes n then
    if hy : ∃ n, y ∈ B.nodes n then c (fun i => ⟨x i, hx i⟩) ⟨y, hy⟩ else default
  else default

omit [Nonempty I] in
theorem ambientVectorLastColor_nodes {K : Type}
    (c : VectorNode T → B.TreeNode → K) (x : VectorNode T) (y : B.TreeNode) :
    ambientVectorLastColor T B c (fun i => (x i).val) y.val = c x y := by
  have hx : ∀ i, ∃ n, (x i).val ∈ (T i).nodes n := fun i => (x i).property
  simp only [ambientVectorLastColor, dif_pos hx, dif_pos y.property]
  have heqx : (fun i => (⟨(x i).val, hx i⟩ : (T i).TreeNode)) = x :=
    funext (fun i => Subtype.ext rfl)
  have heqy : (⟨y.val, y.property⟩ : B.TreeNode) = y := Subtype.ext rfl
  exact congrArg₂ c heqx heqy

/-- The raw constructed section fusion applies to colorings of actual
tree-node vectors, with no source occurrences lost in the extension. -/
theorem section_fusion_live {K : Type} [Fintype K]
    (c : VectorNode T → B.TreeNode → K)
    (hSS : JointFrame.UniformSameDimensionSS (α := α) (R := R)) :
    ∃ e : ℕ → ℕ, ∃ frames : ∀ i, (T i).StrongFrame,
      (∀ i, (frames i).index = e) ∧
        StableVectorSections (fun i => (frames i).toTree) B
          (fun x y => c (fun i => (frames i).nodeMap632 (x i)) y) := by
  obtain ⟨e, _, frames, hindex, hstable⟩ := raw_section_fusion T B (ambientVectorLastColor T B c) hSS
  refine ⟨e, frames, hindex, ?_⟩
  intro n m x y z hx hy hnm hxy hzn
  have hxF : ∀ i, (x i).val ∈ (frames i).nodes n := by
    intro i
    rw [← hx i]
    exact (frames i).toTree.nodeHeight_mem (x i)
  have hyF : ∀ i, (y i).val ∈ (frames i).nodes m := by
    intro i
    rw [← hy i]
    exact (frames i).toTree.nodeHeight_mem (y i)
  have hh := hstable (B.nodeHeight z) z.val (B.nodeHeight_mem z) n m hzn hnm
    (fun i => (x i).val) (fun i => (y i).val) hxF hyF hxy
  have hcx := ambientVectorLastColor_nodes T B c (fun i => (frames i).nodeMap632 (x i)) z
  have hcy := ambientVectorLastColor_nodes T B c (fun i => (frames i).nodeMap632 (y i)) z
  exact hcx.symm.trans (hh.trans hcy)

theorem sectionFusionPrinciple (d : ℕ) (hd : 0 < d) : SectionFusionPrinciple d := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro α _ R T β _ Q B K _ c hSS
  exact section_fusion_live T B c hSS

/-- The full finite-dimensional Halpern--Läuchli theorem for actual
finitely branching infinite trees and arbitrary finite color sets. All
dimensions are proved internally from the one-tree ultrafilter argument,
finite compactness, actual forest fusion, and the branch-color induction. -/
theorem halpernLauchli_all : ∀ d, HalpernLauchliDimension d :=
  halpernLauchli_all_of_section_fusion sectionFusionPrinciple

end RelationalRamsey632.Milliken
