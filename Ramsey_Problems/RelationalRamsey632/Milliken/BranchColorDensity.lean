import RelationalRamsey632.Milliken.ImportedHDHL2
import Mathlib.Logic.Encodable.Basic

/-! The countable branch-color density lemma used in the dimension
induction for Halpern--Läuchli. Its diagonal avoidance proof is internal
and requires no descriptive-set-theoretic or Ramsey axiom. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop} (T : FiniteLevelTree α R)

structure Branch where
  node : (n : ℕ) → {u : α // u ∈ T.nodes n}
  coherent : ∀ n m, n ≤ m → R (node n).val (node m).val

/-- Finite levels imply that the actual nodes of a tree are countable,
regardless of the cardinality of its ambient carrier. -/
instance treeNodeCountable : Countable T.TreeNode := by
  classical
  let f : T.TreeNode → (n : ℕ) × {u : α // u ∈ T.nodes n} :=
    fun u => ⟨T.nodeHeight u, ⟨u.val, T.nodeHeight_mem u⟩⟩
  have hf : Function.Injective f := by
    intro u v h
    exact Subtype.ext (congrArg (fun s : (n : ℕ) × {u : α // u ∈ T.nodes n} => s.2.val) h)
  exact hf.countable

variable {T} in
def Branch.Through (b : Branch T) (u : T.TreeNode) : Prop :=
  (b.node (T.nodeHeight u)).val = u.val

theorem countable_branch_color_dense (g : Branch T → ℕ) :
    ∃ t : T.TreeNode, ∃ k : ℕ,
      ∀ u : T.TreeNode, R t.val u.val →
        ∃ b : Branch T, b.Through u ∧ g b = k := by
  classical
  by_contra hfail
  have havoid : ∀ t : T.TreeNode, ∀ k : ℕ,
      ∃ u : T.TreeNode, R t.val u.val ∧
        ∀ b : Branch T, b.Through u → g b ≠ k := by
    push Not at hfail
    exact hfail
  have hhigh : ∀ t : T.TreeNode, ∀ k : ℕ,
      ∃ u : T.TreeNode, R t.val u.val ∧ k ≤ T.nodeHeight u ∧
        ∀ b : Branch T, b.Through u → g b ≠ k := by
    intro t k
    let n := max (T.nodeHeight t) k
    obtain ⟨v, hv, htv⟩ := T.extend (T.nodeHeight t) n (Nat.le_max_left _ _)
      t.val (T.nodeHeight_mem t)
    let v' : T.TreeNode := ⟨v, n, hv⟩
    obtain ⟨u, hvu, hu⟩ := havoid v' k
    refine ⟨u, T.rel_trans htv hvu, ?_, hu⟩
    have hn : T.nodeHeight v' = n := T.nodeHeight_eq v' n hv
    exact (Nat.le_max_right _ _).trans (hn ▸ T.nodeHeight_le hvu)
  let step := fun t k => Classical.choose (hhigh t k)
  have hstep : ∀ t k, R t.val (step t k).val ∧ k ≤ T.nodeHeight (step t k) ∧
      ∀ b : Branch T, b.Through (step t k) → g b ≠ k :=
    fun t k => Classical.choose_spec (hhigh t k)
  let anchors : ℕ → T.TreeNode :=
    fun n => Nat.rec (step T.rootNode 0) (fun k t => step t (k + 1)) n
  have hheight : ∀ n, n ≤ T.nodeHeight (anchors n) := by
    intro n
    cases n with
    | zero => exact (hstep T.rootNode 0).2.1
    | succ n => exact (hstep (anchors n) (n + 1)).2.1
  have hneg : ∀ n b, b.Through (anchors n) → g b ≠ n := by
    intro n
    cases n with
    | zero => exact (hstep T.rootNode 0).2.2
    | succ n => exact (hstep (anchors n) (n + 1)).2.2
  have hnext : ∀ n, R (anchors n).val (anchors (n + 1)).val :=
    fun n => (hstep (anchors n) (n + 1)).1
  have hchain : ∀ n m, n ≤ m → R (anchors n).val (anchors m).val := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact T.rel_refl _
    | succ m _ ih => exact T.rel_trans ih (hnext m)
  let chosen : (n : ℕ) → {u : α // u ∈ T.nodes n} := fun n =>
    ⟨Classical.choose (T.ancestor n (T.nodeHeight (anchors n)) (hheight n)
      (anchors n).val (T.nodeHeight_mem (anchors n))),
      (Classical.choose_spec (T.ancestor n (T.nodeHeight (anchors n)) (hheight n)
        (anchors n).val (T.nodeHeight_mem (anchors n)))).1.1⟩
  have hchosen : ∀ n, R (chosen n).val (anchors n).val := fun n =>
    (Classical.choose_spec (T.ancestor n (T.nodeHeight (anchors n)) (hheight n)
      (anchors n).val (T.nodeHeight_mem (anchors n)))).1.2
  let b : Branch T := {
    node := chosen
    coherent := fun n m hnm =>
      T.ancestor_comparable n m (T.nodeHeight (anchors m)) hnm
        (chosen n).val (chosen m).val (anchors m).val
        (chosen n).property (chosen m).property (T.nodeHeight_mem (anchors m))
        (T.rel_trans (hchosen n) (hchain n m hnm)) (hchosen m) }
  have hthrough : ∀ k, b.Through (anchors k) := by
    intro k
    let n := T.nodeHeight (anchors k)
    exact T.node_eq_of_common_extension n (T.nodeHeight (anchors n))
      (chosen n).val (anchors k).val (anchors n).val
      (chosen n).property (T.nodeHeight_mem (anchors k)) (T.nodeHeight_mem (anchors n))
      (hchosen n) (hchain k n (hheight k))
  exact hneg (g b) b (hthrough (g b)) rfl

theorem branch_color_dense {K : Type} [Countable K] (g : Branch T → K) :
    ∃ t : T.TreeNode, ∃ k : K,
      ∀ u : T.TreeNode, R t.val u.val →
        ∃ b : Branch T, b.Through u ∧ g b = k := by
  classical
  obtain ⟨encode, hinj⟩ := exists_injective_nat K
  obtain ⟨t, n, ht⟩ := countable_branch_color_dense T (encode ∘ g)
  obtain ⟨b0, _, hb0⟩ := ht t (T.rel_refl _)
  refine ⟨t, g b0, ?_⟩
  intro u hu
  obtain ⟨b, hb, hn⟩ := ht u hu
  exact ⟨b, hb, hinj (hn.trans hb0.symm)⟩

end RelationalRamsey632.Milliken
