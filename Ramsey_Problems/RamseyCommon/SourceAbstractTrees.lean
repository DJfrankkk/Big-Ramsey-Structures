import RamseyCommon.SourceFiniteLevels

/-! Finite-level rooted trees, including whole-level restrictions.

Whole-level restriction is used in the original combinatorial HDHL proof.
It groups several old edges into each new edge and preserves every node
on the retained levels. It is distinct from choosing a strong subtree.
-/

namespace RamseyCommon.SourceTrees

structure FiniteLevelTree (α : Type) (R : α → α → Prop) [DecidableEq α] where
  nodes : ℕ → Finset α
  root : α
  nodes_zero : nodes 0 = {root}
  rel_refl : ∀ u, R u u
  rel_trans : ∀ {u v w}, R u v → R v w → R u w
  rel_antisymm : ∀ {u v}, R u v → R v u → u = v
  level_unique : ∀ n m u, u ∈ nodes n → u ∈ nodes m → n = m
  rel_level : ∀ n m u v, u ∈ nodes n → v ∈ nodes m → R u v → n ≤ m
  ancestor : ∀ n m, n ≤ m → ∀ v ∈ nodes m,
    ∃! u, u ∈ nodes n ∧ R u v
  extend : ∀ n m, n ≤ m → ∀ u ∈ nodes n, ∃ v, v ∈ nodes m ∧ R u v

namespace FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop} (T : FiniteLevelTree α R)

theorem root_mem : T.root ∈ T.nodes 0 := by rw [T.nodes_zero]; simp

theorem nodes_nonempty (n : ℕ) : (T.nodes n).Nonempty := by
  obtain ⟨u, hu, _⟩ := T.extend 0 n (Nat.zero_le n) T.root T.root_mem
  exact ⟨u, hu⟩

def TreeNode := {u : α // ∃ n, u ∈ T.nodes n}

noncomputable def nodeHeight (u : T.TreeNode) : ℕ := Classical.choose u.property

theorem nodeHeight_mem (u : T.TreeNode) : u.val ∈ T.nodes (T.nodeHeight u) :=
  Classical.choose_spec u.property

theorem nodeHeight_eq (u : T.TreeNode) (n : ℕ) (hu : u.val ∈ T.nodes n) :
    T.nodeHeight u = n := T.level_unique _ _ u.val (T.nodeHeight_mem u) hu

theorem nodeHeight_le {u v : T.TreeNode} (hp : R u.val v.val) :
    T.nodeHeight u ≤ T.nodeHeight v :=
  T.rel_level _ _ _ _ (T.nodeHeight_mem u) (T.nodeHeight_mem v) hp

noncomputable def levelNodes (n : ℕ) : Finset T.TreeNode :=
  (T.nodes n).attach.map ⟨fun u => ⟨u.val, n, u.property⟩,
    by intro u v huv; exact Subtype.ext (congrArg (fun w : T.TreeNode => w.val) huv)⟩

theorem mem_levelNodes (n : ℕ) (u : T.TreeNode) : u ∈ T.levelNodes n ↔ u.val ∈ T.nodes n := by
  classical
  constructor
  · intro hu
    obtain ⟨v, _, heq⟩ := Finset.mem_map.mp hu
    have hv : v.val = u.val := congrArg Subtype.val heq
    exact hv ▸ v.property
  · intro hu
    exact Finset.mem_map.mpr ⟨⟨u.val, hu⟩, Finset.mem_attach _ _, by apply Subtype.ext; rfl⟩

theorem nodeHeight_levelNodes (n : ℕ) (u : T.TreeNode) (hu : u ∈ T.levelNodes n) :
    T.nodeHeight u = n := T.nodeHeight_eq u n ((T.mem_levelNodes n u).mp hu)

theorem node_eq_of_common_extension (n m : ℕ) (u v w : α)
    (hu : u ∈ T.nodes n) (hv : v ∈ T.nodes n) (hw : w ∈ T.nodes m)
    (huw : R u w) (hvw : R v w) : u = v := by
  obtain ⟨a, _, ha⟩ := T.ancestor n m (T.rel_level n m u w hu hw huw) w hw
  exact (ha u ⟨hu, huw⟩).trans (ha v ⟨hv, hvw⟩).symm

theorem ancestor_comparable (n m l : ℕ) (hnm : n ≤ m) (u v w : α)
    (hu : u ∈ T.nodes n) (hv : v ∈ T.nodes m) (hw : w ∈ T.nodes l)
    (huw : R u w) (hvw : R v w) : R u v := by
  obtain ⟨a, ⟨ha, hav⟩, _⟩ := T.ancestor n m hnm v hv
  have heq := T.node_eq_of_common_extension n l a u w ha hu hw (T.rel_trans hav hvw) huw
  exact heq ▸ hav

def restrictLevels (index : ℕ → ℕ) (hm : StrictMono index) (hzero : index 0 = 0) :
    FiniteLevelTree α R where
  nodes := fun n => T.nodes (index n)
  root := T.root
  nodes_zero := by rw [hzero, T.nodes_zero]
  rel_refl := T.rel_refl
  rel_trans := T.rel_trans
  rel_antisymm := T.rel_antisymm
  level_unique := fun n m u hn hm' => hm.injective (T.level_unique _ _ u hn hm')
  rel_level := fun n m u v hu hv hr => hm.le_iff_le.mp (T.rel_level _ _ u v hu hv hr)
  ancestor := fun n m hnm v hv => T.ancestor _ _ (hm.monotone hnm) v hv
  extend := fun n m hnm u hu => T.extend _ _ (hm.monotone hnm) u hu

end FiniteLevelTree

namespace StrongPrefixSystem

variable {α : Type} [DecidableEq α] (S : StrongPrefixSystem α)

omit [DecidableEq α] in
private theorem eq_prefixes_of_equal_length {u v w : List α}
    (hu : u <+: w) (hv : v <+: w) (hlen : u.length = v.length) : u = v := by
  rw [List.prefix_iff_eq_take.mp hu, List.prefix_iff_eq_take.mp hv]
  exact congrArg w.take hlen

noncomputable def toFiniteLevelTree : FiniteLevelTree (List α) (· <+: ·) where
  nodes := S.finiteNodes
  root := S.root
  nodes_zero := rfl
  rel_refl := fun u => List.prefix_refl u
  rel_trans := fun hu hv => hu.trans hv
  rel_antisymm := fun hu hv => by
    apply List.IsPrefix.eq_of_length hu
    exact Nat.le_antisymm hu.length_le hv.length_le
  level_unique := by
    intro n m u hu hv
    apply S.level_strictMono.injective
    exact (S.node_length n u ((S.mem_finiteNodes n u).mp hu)).symm.trans
      (S.node_length m u ((S.mem_finiteNodes m u).mp hv))
  rel_level := by
    intro n m u v hu hv hp
    apply S.level_strictMono.le_iff_le.mp
    rw [← S.node_length n u ((S.mem_finiteNodes n u).mp hu),
      ← S.node_length m v ((S.mem_finiteNodes m v).mp hv)]
    exact hp.length_le
  ancestor := by
    intro n m hnm v hv
    obtain ⟨u, hu, hup⟩ := S.ancestor n m hnm v ((S.mem_finiteNodes m v).mp hv)
    refine ⟨u, ⟨(S.mem_finiteNodes n u).mpr hu, hup⟩, ?_⟩
    intro w hw
    exact eq_prefixes_of_equal_length hw.2 hup
      ((S.node_length n w ((S.mem_finiteNodes n w).mp hw.1)).trans (S.node_length n u hu).symm)
  extend := by
    intro n m hnm u hu
    obtain ⟨v, hv, hp⟩ := S.extend n m hnm u ((S.mem_finiteNodes n u).mp hu)
    exact ⟨v, (S.mem_finiteNodes m v).mpr hv, hp⟩

end StrongPrefixSystem

end RamseyCommon.SourceTrees
