import RelationalRamsey632.Milliken.BranchDimension

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    {β : Type} [DecidableEq β] {Q : β → β → Prop} (B : FiniteLevelTree β Q)

def MixedLastMatrixColor {K : Type} (c : VectorNode T → B.TreeNode → K) : Prop :=
  ∃ d, ∃ roots : VectorNode T, ∃ lastRoot : B.TreeNode,
    ∃ columns : ∀ i, Finset (T i).TreeNode, ∃ last : Finset B.TreeNode, ∃ color : K,
      (∀ i, (T i).nodeHeight (roots i) = d) ∧ B.nodeHeight lastRoot = d ∧
      (∀ i, (T i).DenseAbove (roots i) (d + 1) (columns i)) ∧
      B.DenseAbove lastRoot (d + 1) last ∧
      ∀ x ∈ Fintype.piFinset columns, ∀ y ∈ last, c x y = color

/-- Strong-coordinate transport keeps every original immediate successor
cone, so the dimension step yields an actual ambient Cartesian matrix. -/
theorem dimension_matrix_of_stable_frames {K : Type} [Fintype K]
    (hSS : ∀ S : ∀ i, FiniteLevelTree (α i) (R i), StrongSubtreeRamsey S K)
    (c : VectorNode T → B.TreeNode → K)
    (e : ℕ → ℕ) (frames : ∀ i, (T i).StrongFrame)
    (hindex : ∀ i, (frames i).index = e)
    (hst : StableVectorSections (fun i => (frames i).toTree) B
      (fun x y => c (fun i => (frames i).nodeMap632 (x i)) y)) :
    MixedLastMatrixColor T B c := by
  classical
  let T' := fun i => (frames i).toTree
  let map : ∀ i, (T' i).TreeNode → (T i).TreeNode := fun i => (frames i).nodeMap632
  let c' := fun x : VectorNode T' => fun y : B.TreeNode => c (fun i => map i (x i)) y
  obtain ⟨d, _, t, _, hmatrix⟩ := stable_dimension_matrix T' B hSS c' hst
  let D := max d (B.nodeHeight t)
  have hE : D ≤ e D := by
    let i : I := Classical.choice inferInstance
    exact (frames i).index_ge D |>.trans_eq (congrFun (hindex i) D)
  obtain ⟨r, s, columns, last, color, hr, hs, hdense, hlast, hcolor⟩ :=
    hmatrix D (e D) (Nat.le_max_left _ _) ((Nat.le_max_right _ _).trans hE)
  let roots := fun i => map i (r i)
  let output := fun i => (columns i).image (map i)
  refine ⟨e D, roots, s, output, last, color, ?_, hs, ?_, hlast, ?_⟩
  · intro i
    exact ((frames i).nodeMap632_height (r i)).trans
      ((congrArg (frames i).index (hr i)).trans (congrFun (hindex i) D))
  · intro i u hu hru
    have hrF : (r i).val ∈ (frames i).nodes D := by
      rw [← hr i]
      exact (T' i).nodeHeight_mem (r i)
    have huF : u ∈ (T i).nodes ((frames i).index D + 1) := by
      rw [hindex i]
      exact hu
    obtain ⟨w, hw, _⟩ := (frames i).successor D (r i).val hrF u huF hru
    obtain ⟨v, hv, hwv⟩ := hdense i w hw.1 ((T i).rel_trans hru hw.2)
    exact ⟨map i v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, (T i).rel_trans hw.2 hwv⟩
  · intro x hx y hy
    have hpre : ∀ i, ∃ u ∈ columns i, map i u = x i := by
      intro i
      exact Finset.mem_image.mp (Fintype.mem_piFinset.mp hx i)
    choose x' hxmem hxmap using hpre
    have hh := hcolor x' (Fintype.mem_piFinset.mpr hxmem) y hy
    have heq : (fun i => map i (x' i)) = x := funext hxmap
    change c (fun i => map i (x' i)) y = color at hh
    rw [heq] at hh
    exact hh

end RelationalRamsey632.Milliken
