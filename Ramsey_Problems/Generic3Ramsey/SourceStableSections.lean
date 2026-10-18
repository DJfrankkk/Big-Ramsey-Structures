import Generic3Ramsey.SourceAbstractTrees
import Mathlib.Data.Finset.Lattice.Fold

/-! The finite synchronization core in the combinatorial HDHL2 proof.

The input section stability is the property obtained by the preceding
root-preserving fusion. This file proves the finite bad-cone selection
argument: witnesses chosen successively for different second-coordinate
cones are refined jointly so that all earlier negative incidences survive.
-/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α β : Type} [DecidableEq α] [DecidableEq β]
variable {R : α → α → Prop} {Q : β → β → Prop}
variable (S : FiniteLevelTree α R) (T : FiniteLevelTree β Q)

def DenseAbove (x : S.TreeNode) (n : ℕ) (A : Finset S.TreeNode) : Prop :=
  ∀ u, u ∈ S.nodes n → R x.val u → ∃ v ∈ A, R u v.val

def StableSections (P : α → β → Prop) : Prop :=
  ∀ (u v : S.TreeNode) (y : T.TreeNode), T.nodeHeight y < S.nodeHeight u →
    R u.val v.val → (P u.val y.val ↔ P v.val y.val)

def BadCoordinate (P : α → β → Prop) (x : S.TreeNode) (n : ℕ) (y : T.TreeNode) : Prop :=
  ∃ A : Finset S.TreeNode, S.DenseAbove x n A ∧
    ∀ u ∈ A, T.nodeHeight y < S.nodeHeight u ∧ ¬P u.val y.val

omit [DecidableEq β] in
theorem refine_dense_family (x : S.TreeNode) (m n : ℕ) (A D : Finset S.TreeNode)
    (hA : S.DenseAbove x m A) (hroots : ∀ u ∈ A, R x.val u.val)
    (hbound : ∀ u ∈ A, S.nodeHeight u ≤ n) (hD : S.DenseAbove x n D) :
    ∃ B : Finset S.TreeNode, B ⊆ D ∧ S.DenseAbove x m B ∧
      (∀ v ∈ B, R x.val v.val) ∧
      (∀ v ∈ B, ∃ u ∈ A, R u.val v.val) := by
  classical
  have hchoose : ∀ u : {u // u ∈ A}, ∃ v, v ∈ D ∧ R u.val.val v.val := by
    intro u
    obtain ⟨w, hw, huw⟩ := S.extend (S.nodeHeight u.val) n (hbound u.val u.property)
      u.val.val (S.nodeHeight_mem u.val)
    obtain ⟨v, hv, hwv⟩ := hD w hw (S.rel_trans (hroots u.val u.property) huw)
    exact ⟨v, hv, S.rel_trans huw hwv⟩
  choose f hfmem hfext using hchoose
  let B := A.attach.image f
  have hB : ∀ v ∈ B, ∃ u : {u // u ∈ A}, f u = v := by
    intro v hv
    obtain ⟨u, _, huv⟩ := Finset.mem_image.mp hv
    exact ⟨u, huv⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, rfl⟩ := hB v hv
    exact hfmem u
  · intro u hu hxu
    obtain ⟨v, hv, huv⟩ := hA u hu hxu
    refine ⟨f ⟨v, hv⟩, Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩,
      S.rel_trans huv (hfext ⟨v, hv⟩)⟩
  · intro v hv
    obtain ⟨u, rfl⟩ := hB v hv
    exact S.rel_trans (hroots u.val u.property) (hfext u)
  · intro v hv
    obtain ⟨u, rfl⟩ := hB v hv
    exact ⟨u.val, u.property, hfext u⟩

/-- Successive witnesses for a finite second-coordinate frontier can be
made into one genuine negative Cartesian product. The first family remains
dense above the fixed first-coordinate node. -/
theorem bad_coordinates_give_rectangle (P : α → β → Prop)
    (hstable : S.StableSections T P) (x : S.TreeNode) (d : ℕ)
    (F : Finset T.TreeNode)
    (hbad : ∀ y ∈ F, ∀ n ≥ d + 1,
      ∃ z : T.TreeNode, Q y.val z.val ∧ S.BadCoordinate T P x n z) :
    ∃ (A : Finset S.TreeNode) (B : Finset T.TreeNode),
      S.DenseAbove x (d + 1) A ∧
      (∀ u ∈ A, R x.val u.val) ∧
      (∀ y ∈ F, ∃ z ∈ B, Q y.val z.val) ∧
      (∀ u ∈ A, ∀ z ∈ B, T.nodeHeight z < S.nodeHeight u ∧ ¬P u.val z.val) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      let A := (S.levelNodes (d + 1)).filter (fun u => R x.val u.val)
      refine ⟨A, ∅, ?_, ?_, by simp, by simp⟩
      · intro u hu hxu
        let v : S.TreeNode := ⟨u, d + 1, hu⟩
        refine ⟨v, Finset.mem_filter.mpr ⟨(S.mem_levelNodes _ _).mpr hu, hxu⟩, S.rel_refl u⟩
      · intro u hu
        exact (Finset.mem_filter.mp hu).2
  | @insert y F _ ih =>
      obtain ⟨A, B, hA, hroots, hcover, hnegative⟩ := ih (by
        intro z hz n hn
        exact hbad z (Finset.mem_insert_of_mem hz) n hn)
      let n := max (d + 1) (A.sup S.nodeHeight)
      have hn : d + 1 ≤ n := Nat.le_max_left _ _
      obtain ⟨z, hyz, D, hD, hDnegative⟩ := hbad y (Finset.mem_insert_self y F) n hn
      have hbound : ∀ u ∈ A, S.nodeHeight u ≤ n := by
        intro u hu
        exact (Finset.le_sup (f := S.nodeHeight) hu).trans (Nat.le_max_right _ _)
      obtain ⟨A', hA'D, hA', hrootA', hparent⟩ := S.refine_dense_family x (d + 1) n A D
        hA hroots hbound hD
      refine ⟨A', insert z B, hA', hrootA', ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwy | hw
        · subst w
          exact ⟨z, Finset.mem_insert_self z B, hyz⟩
        · obtain ⟨v, hv, hwv⟩ := hcover w hw
          exact ⟨v, Finset.mem_insert_of_mem hv, hwv⟩
      · intro u hu v hv
        rcases Finset.mem_insert.mp hv with hvz | hv
        · subst v
          exact hDnegative u (hA'D hu)
        · obtain ⟨w, hw, hwu⟩ := hparent u hu
          have hneg := hnegative w hw v hv
          refine ⟨hneg.1.trans_le (S.nodeHeight_le hwu), ?_⟩
          intro hp
          exact hneg.2 ((hstable w u v hneg.1 hwu).mpr hp)

end Generic3Ramsey.SourceTrees.FiniteLevelTree
