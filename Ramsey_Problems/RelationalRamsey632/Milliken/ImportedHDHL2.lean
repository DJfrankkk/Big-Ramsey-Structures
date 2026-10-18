import Generic3Ramsey.SourceSectionFusion
import Generic3Ramsey.SourceStableHDHL2

/-! The two-coordinate highly-dense Halpern–Läuchli argument, without a
section-stability premise. Section fusion and its level alignment are actual
constructions, and matrices are transported back through successor cones.
-/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α β : Type} [DecidableEq α] [DecidableEq β]
variable {R : α → α → Prop} {Q : β → β → Prop}
variable (S : FiniteLevelTree α R) (T : FiniteLevelTree β Q)

namespace StrongFrame

variable {S} (F : S.StrongFrame)

noncomputable def nodeMap632 (u : F.toTree.TreeNode) : S.TreeNode :=
  ⟨u.val, F.index (F.toTree.nodeHeight u), F.nodes_subset _ (F.toTree.nodeHeight_mem u)⟩

theorem nodeMap632_height (u : F.toTree.TreeNode) :
    S.nodeHeight (F.nodeMap632 u) = F.index (F.toTree.nodeHeight u) :=
  S.nodeHeight_eq _ _ (F.nodes_subset _ (F.toTree.nodeHeight_mem u))

end StrongFrame

noncomputable def restrictionNodeMap632 (index : ℕ → ℕ) (hm : StrictMono index) (hz : index 0 = 0)
    (u : (T.restrictLevels index hm hz).TreeNode) : T.TreeNode :=
  ⟨u.val, index ((T.restrictLevels index hm hz).nodeHeight u),
    (T.restrictLevels index hm hz).nodeHeight_mem u⟩

theorem restrictionNodeMap632_height (index : ℕ → ℕ) (hm : StrictMono index) (hz : index 0 = 0)
    (u : (T.restrictLevels index hm hz).TreeNode) :
    T.nodeHeight (T.restrictionNodeMap632 index hm hz u) =
      index ((T.restrictLevels index hm hz).nodeHeight u) :=
  T.nodeHeight_eq _ _ ((T.restrictLevels index hm hz).nodeHeight_mem u)

/-- A mixed matrix on a strong first coordinate and the same whole-level
restriction in the second coordinate gives an actual ambient matrix. -/
theorem matrix_transport632 (P : α → β → Prop) (F : S.StrongFrame) (hz : F.index 0 = 0)
    (d : ℕ) (r : F.toTree.TreeNode)
    (s : (T.restrictLevels F.index F.index_strictMono hz).TreeNode)
    (A : Finset F.toTree.TreeNode)
    (B : Finset (T.restrictLevels F.index F.index_strictMono hz).TreeNode)
    (hr : F.toTree.nodeHeight r = d)
    (_hs : (T.restrictLevels F.index F.index_strictMono hz).nodeHeight s = d)
    (hA : F.toTree.DenseAbove r (d + 1) A)
    (hB : (T.restrictLevels F.index F.index_strictMono hz).DenseAbove s (d + 1) B)
    (hmono : ∀ u ∈ A, ∀ v ∈ B, P u.val v.val) :
    ∃ (A' : Finset S.TreeNode) (B' : Finset T.TreeNode),
      S.DenseAbove (F.nodeMap632 r) (F.index d + 1) A' ∧
      T.DenseAbove (T.restrictionNodeMap632 F.index F.index_strictMono hz s) (F.index d + 1) B' ∧
      ∀ u ∈ A', ∀ v ∈ B', P u.val v.val := by
  classical
  let A' := A.image F.nodeMap632
  let B' := B.image (T.restrictionNodeMap632 F.index F.index_strictMono hz)
  refine ⟨A', B', ?_, ?_, ?_⟩
  · intro u hu hru
    have hrF : r.val ∈ F.nodes d := by
      rw [← hr]
      exact F.toTree.nodeHeight_mem r
    obtain ⟨w, ⟨hw, huw⟩, _⟩ := F.successor d r.val hrF u hu hru
    obtain ⟨v, hv, hwv⟩ := hA w hw (S.rel_trans hru huw)
    exact ⟨F.nodeMap632 v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, S.rel_trans huw hwv⟩
  · intro u hu hsu
    obtain ⟨w, hw, huw⟩ := T.extend (F.index d + 1) (F.index (d + 1))
      (F.index_strictMono (Nat.lt_succ_self d)) u hu
    obtain ⟨v, hv, hwv⟩ := hB w hw (T.rel_trans hsu huw)
    exact ⟨T.restrictionNodeMap632 F.index F.index_strictMono hz v,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩, T.rel_trans huw hwv⟩
  · intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact hmono a ha b hb

theorem mixedMatrix_transport632 (P : α → β → Prop) (F : S.StrongFrame) (hz : F.index 0 = 0)
    (h : F.toTree.MixedSomewhereMatrix (T.restrictLevels F.index F.index_strictMono hz) P) :
    S.MixedSomewhereMatrix T P := by
  obtain ⟨d, r, s, A, B, hr, hs, hA, hB, hmono⟩ := h
  obtain ⟨A', B', hA', hB', hmono'⟩ := S.matrix_transport632 T P F hz d r s A B hr hs hA hB hmono
  refine ⟨F.index d, F.nodeMap632 r, T.restrictionNodeMap632 F.index F.index_strictMono hz s,
    A', B', ?_, ?_, hA', hB', hmono'⟩
  · rw [F.nodeMap632_height, hr]
  · rw [T.restrictionNodeMap632_height, hs]

/-- The d=2 highly-dense conclusion from the original combinatorial proof.
No stabilization or rectangular-density theorem is assumed. -/
theorem hdhlTwo632 (P : α → β → Prop)
    (hnegative : ¬S.MixedSomewhereMatrix T (fun u v => ¬P u v)) :
    ∃ (A : Finset S.TreeNode) (B : Finset T.TreeNode),
      S.DenseAbove S.rootNode 1 A ∧ T.DenseAbove T.rootNode 1 B ∧
        ∀ u ∈ A, ∀ v ∈ B, P u.val v.val := by
  classical
  let F := SectionFusion.fusion S T P
  let T' := SectionFusion.otherTree S T P
  have hz : F.index 0 = 0 := SectionFusion.fusion_index_zero S T P
  have hstable : F.toTree.StableSections T' P := SectionFusion.fusion_stable_sections S T P
  have hnegative' : ¬F.toTree.MixedSomewhereMatrix T' (fun u v => ¬P u v) := by
    intro h
    exact hnegative (S.mixedMatrix_transport632 T (fun u v => ¬P u v) F hz h)
  obtain ⟨A, B, hA, hB, hmono⟩ := F.toTree.stable_sections_hdhl2 T' P hstable hnegative'
  obtain ⟨A', B', hA', hB', hmono'⟩ := S.matrix_transport632 T P F hz 0
    F.toTree.rootNode T'.rootNode A B F.toTree.rootNode_height T'.rootNode_height hA hB hmono
  rw [hz] at hA' hB'
  exact ⟨A', B', hA', hB', hmono'⟩

end Generic3Ramsey.SourceTrees.FiniteLevelTree

