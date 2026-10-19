import RelationalRamsey632.Milliken.FiniteColorCompactness
import RelationalRamsey632.Milliken.ImportedHDHL2

/-! The genuine compactness synchronization step for two trees. This is
not asserted to be finite-dimensional vector Milliken: it proves the
synchronized binary somewhere-dense level-matrix consequence. -/

namespace RelationalRamsey632.Milliken

open Filter
open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {α β : Type} [DecidableEq α] [DecidableEq β]
    {R : α → α → Prop} {Q : β → β → Prop}
    (S : FiniteLevelTree α R) (T : FiniteLevelTree β Q)

structure TwoTreeMatrix where
  depth : ℕ
  firstRoot : S.TreeNode
  secondRoot : T.TreeNode
  firstRoot_height : S.nodeHeight firstRoot = depth
  secondRoot_height : T.nodeHeight secondRoot = depth
  rows : Finset S.TreeNode
  columns : Finset T.TreeNode
  rows_dense : S.DenseAbove firstRoot (depth + 1) rows
  columns_dense : T.DenseAbove secondRoot (depth + 1) columns

namespace TwoTreeMatrix

variable {S T} (D : TwoTreeMatrix S T)

def support : Finset (S.TreeNode × T.TreeNode) := D.rows.product D.columns

theorem rows_nonempty : D.rows.Nonempty := by
  obtain ⟨u, hu, hru⟩ := S.extend D.depth (D.depth + 1) (Nat.le_succ _)
    D.firstRoot.val (D.firstRoot_height ▸ S.nodeHeight_mem D.firstRoot)
  obtain ⟨v, hv, _⟩ := D.rows_dense u hu hru
  exact ⟨v, hv⟩

theorem columns_nonempty : D.columns.Nonempty := by
  obtain ⟨u, hu, hru⟩ := T.extend D.depth (D.depth + 1) (Nat.le_succ _)
    D.secondRoot.val (D.secondRoot_height ▸ T.nodeHeight_mem D.secondRoot)
  obtain ⟨v, hv, _⟩ := D.columns_dense u hu hru
  exact ⟨v, hv⟩

end TwoTreeMatrix

noncomputable def ambientColor (c : S.TreeNode × T.TreeNode → Bool)
    (a : α) (b : β) : Bool := by
  classical
  exact if ha : ∃ n, a ∈ S.nodes n then
    if hb : ∃ n, b ∈ T.nodes n then c (⟨a, ha⟩, ⟨b, hb⟩) else false
  else false

@[simp] theorem ambientColor_node (c : S.TreeNode × T.TreeNode → Bool)
    (a : S.TreeNode) (b : T.TreeNode) : ambientColor S T c a.val b.val = c (a, b) := by
  simp only [ambientColor, dif_pos a.property, dif_pos b.property]
  apply congrArg c
  exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

/-- The proved mixed-height HDHL2 theorem really gives the binary mixed
SDHL theorem, including both color outcomes. -/
theorem mixed_binary_matrix (c : S.TreeNode × T.TreeNode → Bool) :
    ∃ D : TwoTreeMatrix S T, Monochromatic c D.support := by
  classical
  let P := fun a b => ambientColor S T c a b = true
  by_cases hneg : S.MixedSomewhereMatrix T (fun a b => ¬P a b)
  · obtain ⟨d, r, s, A, B, hr, hs, hA, hB, hmono⟩ := hneg
    let D : TwoTreeMatrix S T := ⟨d, r, s, hr, hs, A, B, hA, hB⟩
    have hc : ∀ a ∈ A, ∀ b ∈ B, c (a, b) = false := by
      intro a ha b hb
      have hh := hmono a ha b hb
      change ambientColor S T c a.val b.val ≠ true at hh
      rw [ambientColor_node] at hh
      cases hv : c (a, b) with
      | false => rfl
      | true => exact (hh hv).elim
    refine ⟨D, ?_⟩
    intro x hx y hy
    exact (hc x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2).trans
      (hc y.1 (Finset.mem_product.mp hy).1 y.2 (Finset.mem_product.mp hy).2).symm
  · obtain ⟨A, B, hA, hB, hmono⟩ := S.hdhlTwo632 T P hneg
    let D : TwoTreeMatrix S T := ⟨0, S.rootNode, T.rootNode,
      S.rootNode_height, T.rootNode_height, A, B, hA, hB⟩
    have hc : ∀ a ∈ A, ∀ b ∈ B, c (a, b) = true := by
      intro a ha b hb
      have hh := hmono a ha b hb
      change ambientColor S T c a.val b.val = true at hh
      simpa only [ambientColor_node] using hh
    refine ⟨D, ?_⟩
    intro x hx y hy
    exact (hc x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2).trans
      (hc y.1 (Finset.mem_product.mp hy).1 y.2 (Finset.mem_product.mp hy).2).symm

noncomputable def boundedNodes (N : ℕ) : Finset S.TreeNode := by
  classical
  exact (Finset.range (N + 1)).biUnion S.levelNodes

theorem mem_boundedNodes (N : ℕ) (u : S.TreeNode) :
    u ∈ boundedNodes S N ↔ S.nodeHeight u ≤ N := by
  classical
  constructor
  · intro hu
    obtain ⟨n, hn, hu⟩ := Finset.mem_biUnion.mp hu
    have hh := S.nodeHeight_levelNodes n u hu
    have hn' := Finset.mem_range.mp hn
    omega
  · intro hu
    exact Finset.mem_biUnion.mpr ⟨S.nodeHeight u, Finset.mem_range.mpr (by omega),
      (S.mem_levelNodes _ _).mpr (S.nodeHeight_mem u)⟩

theorem finite_binary_matrix_bound :
    ∃ N, ∀ c : S.TreeNode × T.TreeNode → Bool,
      ∃ D : TwoTreeMatrix S T,
        D.support ⊆ (boundedNodes S N).product (boundedNodes T N) ∧
          Monochromatic c D.support := by
  have hc : ∀ x : S.TreeNode × T.TreeNode, ∀ᶠ N in atTop,
      x ∈ (boundedNodes S N).product (boundedNodes T N) := by
    intro x
    apply (eventually_ge_atTop (max (S.nodeHeight x.1) (T.nodeHeight x.2))).mono
    intro N hN
    exact Finset.mem_product.mpr
      ⟨(mem_boundedNodes S N x.1).mpr ((Nat.le_max_left _ _).trans hN),
       (mem_boundedNodes T N x.2).mpr ((Nat.le_max_right _ _).trans hN)⟩
  obtain ⟨N, hN⟩ := finite_color_compactness
    (fun D : TwoTreeMatrix S T => D.support) (fun _ => True)
    (fun N => (boundedNodes S N).product (boundedNodes T N)) hc
    (fun c => by obtain ⟨D, hD⟩ := mixed_binary_matrix S T c; exact ⟨D, trivial, hD⟩)
  exact ⟨N, fun c => by obtain ⟨D, _, hD, hm⟩ := hN c; exact ⟨D, hD, hm⟩⟩

noncomputable def raiseNode (N : ℕ) (u : S.TreeNode) : S.TreeNode := by
  classical
  by_cases hu : S.nodeHeight u ≤ N
  · let v := Classical.choose (S.extend (S.nodeHeight u) N hu u.val (S.nodeHeight_mem u))
    exact ⟨v, N, (Classical.choose_spec (S.extend (S.nodeHeight u) N hu u.val (S.nodeHeight_mem u))).1⟩
  · let v := Classical.choose (S.extend 0 N (Nat.zero_le _) S.root S.root_mem)
    exact ⟨v, N, (Classical.choose_spec (S.extend 0 N (Nat.zero_le _) S.root S.root_mem)).1⟩

theorem raiseNode_height (N : ℕ) (u : S.TreeNode) : S.nodeHeight (raiseNode S N u) = N := by
  classical
  unfold raiseNode
  split_ifs with hu
  · exact S.nodeHeight_eq _ N (Classical.choose_spec
      (S.extend (S.nodeHeight u) N hu u.val (S.nodeHeight_mem u))).1
  · exact S.nodeHeight_eq _ N (Classical.choose_spec
      (S.extend 0 N (Nat.zero_le _) S.root S.root_mem)).1

theorem raiseNode_extends (N : ℕ) (u : S.TreeNode) (hu : S.nodeHeight u ≤ N) :
    R u.val (raiseNode S N u).val := by
  classical
  unfold raiseNode
  simp only [dif_pos hu]
  exact (Classical.choose_spec (S.extend (S.nodeHeight u) N hu u.val (S.nodeHeight_mem u))).2

/-- A true synchronized binary dense rectangle. Both output families lie
on one common level, obtained by pushing a uniform finite compactness
witness to that level. -/
theorem synchronized_binary_dense_matrix (c : S.TreeNode × T.TreeNode → Bool) :
    ∃ N, ∃ D : TwoTreeMatrix S T,
      (∀ u ∈ D.rows, S.nodeHeight u = N) ∧
      (∀ v ∈ D.columns, T.nodeHeight v = N) ∧ Monochromatic c D.support := by
  classical
  obtain ⟨N, hN⟩ := finite_binary_matrix_bound S T
  let cN := fun x : S.TreeNode × T.TreeNode => c (raiseNode S N x.1, raiseNode T N x.2)
  obtain ⟨D, hbound, hmono⟩ := hN cN
  obtain ⟨u0, hu0⟩ := D.rows_nonempty
  obtain ⟨v0, hv0⟩ := D.columns_nonempty
  have hrow : ∀ u ∈ D.rows, S.nodeHeight u ≤ N := by
    intro u hu
    have hh := Finset.mem_product.mp
      (hbound (show (u, v0) ∈ D.support from Finset.mem_product.mpr ⟨hu, hv0⟩))
    exact (mem_boundedNodes S N u).mp hh.1
  have hcol : ∀ v ∈ D.columns, T.nodeHeight v ≤ N := by
    intro v hv
    have hh := Finset.mem_product.mp
      (hbound (show (u0, v) ∈ D.support from Finset.mem_product.mpr ⟨hu0, hv⟩))
    exact (mem_boundedNodes T N v).mp hh.2
  let rows := D.rows.image (raiseNode S N)
  let columns := D.columns.image (raiseNode T N)
  have hdenseR : S.DenseAbove D.firstRoot (D.depth + 1) rows := by
    intro u hu hru
    obtain ⟨v, hv, huv⟩ := D.rows_dense u hu hru
    exact ⟨raiseNode S N v, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      S.rel_trans huv (raiseNode_extends S N v (hrow v hv))⟩
  have hdenseC : T.DenseAbove D.secondRoot (D.depth + 1) columns := by
    intro u hu hru
    obtain ⟨v, hv, huv⟩ := D.columns_dense u hu hru
    exact ⟨raiseNode T N v, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      T.rel_trans huv (raiseNode_extends T N v (hcol v hv))⟩
  let D' : TwoTreeMatrix S T := ⟨D.depth, D.firstRoot, D.secondRoot,
    D.firstRoot_height, D.secondRoot_height, rows, columns, hdenseR, hdenseC⟩
  refine ⟨N, D', ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact raiseNode_height S N v
  · intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact raiseNode_height T N v
  · intro x hx y hy
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp (Finset.mem_product.mp hx).1
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp (Finset.mem_product.mp hx).2
    obtain ⟨a', ha', hay⟩ := Finset.mem_image.mp (Finset.mem_product.mp hy).1
    obtain ⟨b', hb', hby⟩ := Finset.mem_image.mp (Finset.mem_product.mp hy).2
    have hh := hmono (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
      (a', b') (Finset.mem_product.mpr ⟨ha', hb'⟩)
    change c (raiseNode S N a, raiseNode T N b) = c (raiseNode S N a', raiseNode T N b') at hh
    simpa only [hax, hbx, hay, hby] using hh

end RelationalRamsey632.Milliken

