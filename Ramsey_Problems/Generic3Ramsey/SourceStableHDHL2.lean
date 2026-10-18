import Generic3Ramsey.SourceDenseSelection

/-! The two-coordinate HDHL conclusion after the section-stabilization
fusion, with the finite-coordinate selection proved in `SourceDenseSelection`.
-/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α β : Type} [DecidableEq α] [DecidableEq β]
variable {R : α → α → Prop} {Q : β → β → Prop}
variable (S : FiniteLevelTree α R) (T : FiniteLevelTree β Q)

def rootNode : S.TreeNode := ⟨S.root, 0, S.root_mem⟩

theorem rootNode_height : S.nodeHeight S.rootNode = 0 := S.nodeHeight_eq _ _ S.root_mem

theorem root_below_node (u : S.TreeNode) : R S.root u.val := by
  obtain ⟨v, ⟨hv, hp⟩, _⟩ := S.ancestor 0 (S.nodeHeight u) (Nat.zero_le _)
    u.val (S.nodeHeight_mem u)
  rw [S.nodes_zero, Finset.mem_singleton] at hv
  exact hv ▸ hp

theorem not_badCoordinate_positive_cone (P : α → β → Prop) (x : S.TreeNode)
    (n : ℕ) (y : T.TreeNode) (hnot : ¬S.BadCoordinate T P x n y) :
    ∃ u ∈ S.nodes n, R x.val u ∧
      ∀ v : S.TreeNode, R u v.val → T.nodeHeight y < S.nodeHeight v → P v.val y.val := by
  classical
  by_contra hnone
  let F := (S.levelNodes n).filter (fun u => R x.val u.val)
  have hchoose : ∀ u : {u // u ∈ F},
      ∃ v : S.TreeNode, R u.val.val v.val ∧ T.nodeHeight y < S.nodeHeight v ∧ ¬P v.val y.val := by
    intro u
    have hnot' : ¬∀ v : S.TreeNode, R u.val.val v.val →
        T.nodeHeight y < S.nodeHeight v → P v.val y.val := by
      intro hp
      exact hnone ⟨u.val.val, (S.mem_levelNodes n u.val).mp (Finset.mem_filter.mp u.property).1,
        (Finset.mem_filter.mp u.property).2, hp⟩
    push Not at hnot'
    exact hnot'
  choose f hfcone hfhigh hfneg using hchoose
  apply hnot
  refine ⟨F.attach.image f, ?_, ?_⟩
  · intro u hu hxu
    let u' : S.TreeNode := ⟨u, n, hu⟩
    have huF : u' ∈ F := Finset.mem_filter.mpr ⟨(S.mem_levelNodes _ _).mpr hu, hxu⟩
    exact ⟨f ⟨u', huF⟩, Finset.mem_image.mpr ⟨⟨u', huF⟩, Finset.mem_attach _ _, rfl⟩,
      hfcone ⟨u', huF⟩⟩
  · intro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨hfhigh u, hfneg u⟩

theorem positive_dense_family_of_noBad (P : α → β → Prop) (k n : ℕ) (y : T.TreeNode)
    (hgood : ∀ x ∈ S.levelNodes k, ¬S.BadCoordinate T P x n y) :
    ∃ A : Finset S.TreeNode, S.DenseAbove S.rootNode k A ∧
      ∀ u ∈ A, T.nodeHeight y < S.nodeHeight u ∧ P u.val y.val := by
  classical
  let N := max n (T.nodeHeight y + 1)
  have hchoose : ∀ x : {x // x ∈ S.levelNodes k},
      ∃ v : S.TreeNode, R x.val.val v.val ∧ T.nodeHeight y < S.nodeHeight v ∧ P v.val y.val := by
    intro x
    obtain ⟨u, hu, hxu, hpositive⟩ := S.not_badCoordinate_positive_cone T P x.val n y
      (hgood x.val x.property)
    obtain ⟨v, hv, huv⟩ := S.extend n N (Nat.le_max_left _ _) u hu
    let v' : S.TreeNode := ⟨v, N, hv⟩
    have hhigh : T.nodeHeight y < S.nodeHeight v' := by
      rw [S.nodeHeight_eq v' N hv]
      exact (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)
    exact ⟨v', S.rel_trans hxu huv, hhigh, hpositive v' huv hhigh⟩
  choose f hfcone hfhigh hfpositive using hchoose
  refine ⟨(S.levelNodes k).attach.image f, ?_, ?_⟩
  · intro u hu _
    let u' : S.TreeNode := ⟨u, k, hu⟩
    have huK := (S.mem_levelNodes k u').mpr hu
    exact ⟨f ⟨u', huK⟩, Finset.mem_image.mpr ⟨⟨u', huK⟩, Finset.mem_attach _ _, rfl⟩,
      hfcone ⟨u', huK⟩⟩
  · intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨hfhigh x, hfpositive x⟩

/-- The d=2 specialization of the positive-section step: one chosen
second-coordinate extension supports a globally k-dense first family. -/
theorem stable_positive_section (P : α → β → Prop) (hstable : S.StableSections T P)
    (hnegative : ¬S.MixedSomewhereMatrix T (fun u v => ¬P u v))
    (t : T.TreeNode) (k : ℕ) :
    ∃ y : T.TreeNode, Q t.val y.val ∧
      ∃ A : Finset S.TreeNode, S.DenseAbove S.rootNode k A ∧
        ∀ u ∈ A, T.nodeHeight y < S.nodeHeight u ∧ P u.val y.val := by
  let X : Set T.TreeNode := {y | Q t.val y.val}
  have hX : T.SomewhereTauDense X := by
    refine ⟨t, ?_⟩
    intro u htu
    exact ⟨u, htu, T.rel_refl u.val⟩
  obtain ⟨n, z, hfamily⟩ := S.stable_sections_dense_good_family T P hstable hnegative k
    (S.levelNodes k) (S.nodeHeight_levelNodes k) X hX
  obtain ⟨y, hy, _⟩ := hfamily z (T.rel_refl z.val)
  obtain ⟨A, hA, hpositive⟩ := S.positive_dense_family_of_noBad T P k n y hy.2
  exact ⟨y, hy.1, A, hA, hpositive⟩

/-- The actual HDHL2 Cartesian-product conclusion under the section
stability produced by fusion. It does not assume a dense rectangle exists. -/
theorem stable_sections_hdhl2 (P : α → β → Prop) (hstable : S.StableSections T P)
    (hnegative : ¬S.MixedSomewhereMatrix T (fun u v => ¬P u v)) :
    ∃ (A : Finset S.TreeNode) (B : Finset T.TreeNode),
      S.DenseAbove S.rootNode 1 A ∧ T.DenseAbove T.rootNode 1 B ∧
        ∀ u ∈ A, ∀ v ∈ B, P u.val v.val := by
  classical
  have hstableNeg : S.StableSections T (fun u v => ¬P u v) := by
    intro u v y hhigh huv
    exact not_congr (hstable u v y hhigh huv)
  have hbad : ∀ y ∈ T.levelNodes 1, ∀ n ≥ 0 + 1,
      ∃ z : T.TreeNode, Q y.val z.val ∧ S.BadCoordinate T (fun u v => ¬P u v) S.rootNode n z := by
    intro y _ n _
    obtain ⟨z, hyz, A, hA, hpositive⟩ := S.stable_positive_section T P hstable hnegative y n
    refine ⟨z, hyz, A, hA, ?_⟩
    intro u hu
    exact ⟨(hpositive u hu).1, not_not.mpr (hpositive u hu).2⟩
  obtain ⟨A, B, hA, _, hB, hAB⟩ := S.bad_coordinates_give_rectangle T
    (fun u v => ¬P u v) hstableNeg S.rootNode 0 (T.levelNodes 1) hbad
  refine ⟨A, B, hA, ?_, ?_⟩
  · intro u hu _
    let u' : T.TreeNode := ⟨u, 1, hu⟩
    exact hB u' ((T.mem_levelNodes 1 u').mpr hu)
  · intro u hu v hv
    exact not_not.mp (hAB u hu v hv).2

end Generic3Ramsey.SourceTrees.FiniteLevelTree
