import Generic3Ramsey.SourceAbstractTrees

/-! Strong-subtree data over finite-level trees and its actual induced tree. -/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
variable (T : FiniteLevelTree α R)

structure StrongFrame where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  nodes : ℕ → Finset α
  root : α
  nodes_zero : nodes 0 = {root}
  nodes_subset : ∀ n, nodes n ⊆ T.nodes (index n)
  parent : ∀ n w, w ∈ nodes (n + 1) → ∃ u ∈ nodes n, R u w
  successor : ∀ n u, u ∈ nodes n → ∀ v ∈ T.nodes (index n + 1), R u v →
    ∃! w, w ∈ nodes (n + 1) ∧ R v w

namespace StrongFrame

variable {T} (F : T.StrongFrame)

def identity (T : FiniteLevelTree α R) : T.StrongFrame where
  index := id
  index_strictMono := strictMono_id
  nodes := T.nodes
  root := T.root
  nodes_zero := T.nodes_zero
  nodes_subset := fun n => Finset.Subset.refl (T.nodes n)
  parent := by
    intro n w hw
    obtain ⟨u, ⟨hu, huw⟩, _⟩ := T.ancestor n (n + 1) (Nat.le_succ n) w hw
    exact ⟨u, hu, huw⟩
  successor := by
    intro n u hu v hv huv
    refine ⟨v, ⟨hv, T.rel_refl v⟩, ?_⟩
    intro w hw
    exact T.node_eq_of_common_extension (n + 1) (n + 1) w v w hw.1 hv hw.1 (T.rel_refl w) hw.2

theorem ancestor (n m : ℕ) (hnm : n ≤ m) (w : α) (hw : w ∈ F.nodes m) :
    ∃! u, u ∈ F.nodes n ∧ R u w := by
  have hex : ∃ u, u ∈ F.nodes n ∧ R u w := by
    induction m generalizing n w with
    | zero =>
        have hn : n = 0 := by omega
        subst n
        exact ⟨w, hw, T.rel_refl w⟩
    | succ m ih =>
        by_cases hn : n = m + 1
        · subst n
          exact ⟨w, hw, T.rel_refl w⟩
        · obtain ⟨v, hv, hvw⟩ := F.parent m w hw
          obtain ⟨u, hu, huv⟩ := ih n (by omega) v hv
          exact ⟨u, hu, T.rel_trans huv hvw⟩
  obtain ⟨u, hu, huw⟩ := hex
  refine ⟨u, ⟨hu, huw⟩, ?_⟩
  intro v hv
  exact T.node_eq_of_common_extension (F.index n) (F.index m) v u w
    (F.nodes_subset n hv.1) (F.nodes_subset n hu) (F.nodes_subset m hw) hv.2 huw

theorem extend (n m : ℕ) (hnm : n ≤ m) (u : α) (hu : u ∈ F.nodes n) :
    ∃ w, w ∈ F.nodes m ∧ R u w := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨u, hu, T.rel_refl u⟩
  | succ m hnm ih =>
      obtain ⟨v, hv, huv⟩ := ih
      obtain ⟨a, ha, hva⟩ := T.extend (F.index m) (F.index m + 1) (Nat.le_succ _)
        v (F.nodes_subset m hv)
      obtain ⟨w, ⟨hw, haw⟩, _⟩ := F.successor m v hv a ha hva
      exact ⟨w, hw, T.rel_trans huv (T.rel_trans hva haw)⟩

def toTree : FiniteLevelTree α R where
  nodes := F.nodes
  root := F.root
  nodes_zero := F.nodes_zero
  rel_refl := T.rel_refl
  rel_trans := T.rel_trans
  rel_antisymm := T.rel_antisymm
  level_unique := fun n m u hu hv => F.index_strictMono.injective
    (T.level_unique _ _ u (F.nodes_subset n hu) (F.nodes_subset m hv))
  rel_level := fun n m u v hu hv huv => F.index_strictMono.le_iff_le.mp
    (T.rel_level _ _ u v (F.nodes_subset n hu) (F.nodes_subset m hv) huv)
  ancestor := F.ancestor
  extend := F.extend

/-- Strongness is transitive, with the actual two successor-cone steps. -/
def comp (G : F.toTree.StrongFrame) : T.StrongFrame where
  index := fun n => F.index (G.index n)
  index_strictMono := F.index_strictMono.comp G.index_strictMono
  nodes := G.nodes
  root := G.root
  nodes_zero := G.nodes_zero
  nodes_subset := fun n => (G.nodes_subset n).trans (F.nodes_subset (G.index n))
  parent := G.parent
  successor := by
    intro n u hu v hv huv
    have huF : u ∈ F.nodes (G.index n) := G.nodes_subset n hu
    obtain ⟨w, ⟨hw, hvw⟩, hwunique⟩ := F.successor (G.index n) u huF v hv huv
    obtain ⟨z, ⟨hz, hwz⟩, hzunique⟩ := G.successor n u hu w hw (T.rel_trans huv hvw)
    refine ⟨z, ⟨hz, T.rel_trans hvw hwz⟩, ?_⟩
    intro z' hz'
    have hz'F : z' ∈ F.nodes (G.index (n + 1)) := G.nodes_subset (n + 1) hz'.1
    obtain ⟨w', ⟨hw', hw'z'⟩, _⟩ := F.ancestor (G.index n + 1) (G.index (n + 1))
      (G.index_strictMono (Nat.lt_succ_self n)) z' hz'F
    have hcomp : R v w' := T.ancestor_comparable (F.index (G.index n) + 1)
      (F.index (G.index n + 1)) (F.index (G.index (n + 1)))
      (F.index_strictMono (Nat.lt_succ_self (G.index n))) v w' z' hv
      (F.nodes_subset _ hw') (F.nodes_subset _ hz'F) hz'.2 hw'z'
    have heq : w' = w := hwunique w' ⟨hw', hcomp⟩
    exact hzunique z' ⟨hz'.1, heq ▸ hw'z'⟩

theorem toTree_comp (G : F.toTree.StrongFrame) : (F.comp G).toTree = G.toTree := rfl

theorem comp_assoc (G : F.toTree.StrongFrame) (H : G.toTree.StrongFrame) :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

theorem index_ge (n : ℕ) : n ≤ F.index n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (F.index_strictMono (Nat.lt_succ_self n)))

end StrongFrame

end Generic3Ramsey.SourceTrees.FiniteLevelTree
