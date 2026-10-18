import Generic3Ramsey.SourceColoredForests
import Generic3Ramsey.SourceStrongFrames

/-! Root-preserving tail stabilization for one finite coloring. -/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

open Filter

variable {α K : Type} [DecidableEq α] [Fintype K] {R : α → α → Prop}
variable (T : FiniteLevelTree α R)

def AnchorIndex (m : ℕ) := {u : T.TreeNode // u ∈ T.levelNodes (m + 1)}

noncomputable instance anchorIndex_fintype (m : ℕ) : Fintype (T.AnchorIndex m) := by
  classical
  change Fintype {u : T.TreeNode // u ∈ T.levelNodes (m + 1)}
  infer_instance

structure TailData (c : α → K) (U : Ultrafilter ℕ) (m : ℕ) where
  data : T.ColorRoots (I := T.AnchorIndex m) c U
  anchor_below_root : ∀ i, R i.val.val (data.root i).val
  initial : data.Stage
  initial_index : m < initial.index
  initial_singleton : ∀ i, ∃ u, initial.nodes i = {u}

theorem tailData_exists (c : α → K) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (m : ℕ) :
    Nonempty (T.TailData c U m) := by
  classical
  obtain ⟨D, hD⟩ := T.colorRoots_above c U hU (fun i : T.AnchorIndex m => i.val)
  obtain ⟨A, hA, hsingle⟩ := D.initial_stage_exists hU m
  exact ⟨⟨D, hD, A, hA, hsingle⟩⟩

namespace TailData

omit [Fintype K]
variable {T} {c : α → K} {U : Ultrafilter ℕ} {m : ℕ}
variable (D : T.TailData c U m) (hU : (U : Filter ℕ) ≤ atTop)

noncomputable def stages (hU : (U : Filter ℕ) ≤ atTop) := D.data.stages D.initial hU

theorem index_gt (n : ℕ) : m < (D.stages hU n).index :=
  D.initial_index.trans_le ((D.data.stages_index_strictMono D.initial hU).monotone (Nat.zero_le n))

noncomputable def tailNodes (hU : (U : Filter ℕ) ≤ atTop) (n : ℕ) : Finset α :=
  Finset.univ.biUnion fun i : T.AnchorIndex m => ((D.stages hU n).nodes i).image Subtype.val

theorem mem_tailNodes (n : ℕ) (w : α) : w ∈ D.tailNodes hU n ↔
    ∃ (i : T.AnchorIndex m) (u : T.TreeNode), u ∈ (D.stages hU n).nodes i ∧ u.val = w := by
  classical
  constructor
  · intro hw
    obtain ⟨i, _, hu⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hu
    exact ⟨i, u, hu, heq⟩
  · rintro ⟨i, u, hu, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem tailNodes_subset (n : ℕ) : D.tailNodes hU n ⊆ T.nodes (D.stages hU n).index := by
  intro w hw
  obtain ⟨i, u, hu, rfl⟩ := (D.mem_tailNodes hU n w).mp hw
  rw [← (D.stages hU n).height i u hu]
  exact T.nodeHeight_mem u

theorem anchor_below (n : ℕ) (i : T.AnchorIndex m) (u : T.TreeNode)
    (hu : u ∈ (D.stages hU n).nodes i) : R i.val.val u.val :=
  T.rel_trans (D.anchor_below_root i) ((D.stages hU n).below_root i u hu)

theorem anchor_eq_of_common_extension (i j : T.AnchorIndex m) (n : ℕ) (w : α)
    (hw : w ∈ T.nodes n) (hi : R i.val.val w) (hj : R j.val.val w) : i = j := by
  apply Subtype.ext
  apply Subtype.ext
  exact T.node_eq_of_common_extension (m + 1) n _ _ w
    ((T.mem_levelNodes _ _).mp i.property) ((T.mem_levelNodes _ _).mp j.property) hw hi hj

noncomputable def joinedIndex (hU : (U : Filter ℕ) ≤ atTop) (n : ℕ) : ℕ :=
  if n ≤ m then n else (D.stages hU (n - m - 1)).index

noncomputable def joinedNodes (hU : (U : Filter ℕ) ≤ atTop) (n : ℕ) : Finset α :=
  if n ≤ m then T.nodes n else D.tailNodes hU (n - m - 1)

theorem joinedIndex_initial (n : ℕ) (hn : n ≤ m) : D.joinedIndex hU n = n := by
  simp only [joinedIndex, if_pos hn]

theorem joinedNodes_initial (n : ℕ) (hn : n ≤ m) : D.joinedNodes hU n = T.nodes n := by
  simp only [joinedNodes, if_pos hn]

theorem joinedIndex_tail (n : ℕ) : D.joinedIndex hU (m + 1 + n) = (D.stages hU n).index := by
  simp only [joinedIndex, if_neg (show ¬m + 1 + n ≤ m by omega)]
  rw [show m + 1 + n - m - 1 = n by omega]

theorem joinedNodes_tail (n : ℕ) : D.joinedNodes hU (m + 1 + n) = D.tailNodes hU n := by
  simp only [joinedNodes, if_neg (show ¬m + 1 + n ≤ m by omega)]
  rw [show m + 1 + n - m - 1 = n by omega]

theorem joinedIndex_strictMono : StrictMono (D.joinedIndex hU) := by
  intro n p hnp
  by_cases hn : n ≤ m
  · rw [D.joinedIndex_initial hU n hn]
    by_cases hp : p ≤ m
    · rw [D.joinedIndex_initial hU p hp]
      exact hnp
    · simp only [joinedIndex, if_neg hp]
      exact hn.trans_lt (D.index_gt hU _)
  · have hp : ¬p ≤ m := by omega
    simp only [joinedIndex, if_neg hn, if_neg hp]
    apply D.data.stages_index_strictMono D.initial hU
    all_goals omega

theorem joinedNodes_subset (n : ℕ) : D.joinedNodes hU n ⊆ T.nodes (D.joinedIndex hU n) := by
  by_cases hn : n ≤ m
  · rw [D.joinedNodes_initial hU n hn, D.joinedIndex_initial hU n hn]
  · simp only [joinedNodes, joinedIndex, if_neg hn]
    exact D.tailNodes_subset hU _

theorem tailNodes_parent (n : ℕ) (w : α) (hw : w ∈ D.tailNodes hU (n + 1)) :
    ∃ u ∈ D.tailNodes hU n, R u w := by
  classical
  obtain ⟨i, w', hw', rfl⟩ := (D.mem_tailNodes hU (n + 1) w).mp hw
  obtain ⟨u, hu, v, hv, hvw⟩ := D.data.stages_parent D.initial hU n i w' hw'
  exact ⟨u.val, (D.mem_tailNodes hU n u.val).mpr ⟨i, u, hu, rfl⟩,
    T.rel_trans (Finset.mem_filter.mp hv).2 hvw⟩

theorem tailNodes_successor (n : ℕ) (u : α) (hu : u ∈ D.tailNodes hU n)
    (v : α) (hv : v ∈ T.nodes ((D.stages hU n).index + 1)) (huv : R u v) :
    ∃! w, w ∈ D.tailNodes hU (n + 1) ∧ R v w := by
  classical
  obtain ⟨i, u', hu', rfl⟩ := (D.mem_tailNodes hU n u).mp hu
  let v' : T.TreeNode := ⟨v, (D.stages hU n).index + 1, hv⟩
  have hv' : v' ∈ (D.stages hU n).children u' :=
    Finset.mem_filter.mpr ⟨(T.mem_levelNodes _ _).mpr hv, huv⟩
  obtain ⟨w', ⟨hw', hvw⟩, huniq⟩ := D.data.stages_successor D.initial hU n i u' hu' v' hv'
  refine ⟨w'.val, ⟨(D.mem_tailNodes hU (n + 1) w'.val).mpr ⟨i, w', hw', rfl⟩, hvw⟩, ?_⟩
  intro w hw
  obtain ⟨j, z, hz, rfl⟩ := (D.mem_tailNodes hU (n + 1) w).mp hw.1
  have hzw : z.val ∈ T.nodes (D.stages hU (n + 1)).index := by
    rw [← (D.stages hU (n + 1)).height j z hz]
    exact T.nodeHeight_mem z
  have heq : j = i := anchor_eq_of_common_extension j i _ z.val hzw
    (D.anchor_below hU (n + 1) j z hz)
    (T.rel_trans (D.anchor_below hU n i u' hu') (T.rel_trans huv hw.2))
  subst j
  exact congrArg Subtype.val (huniq z ⟨hz, hw.2⟩)

theorem boundary_successor (v : α) (hv : v ∈ T.nodes (m + 1)) :
    ∃! w, w ∈ D.tailNodes hU 0 ∧ R v w := by
  classical
  let v' : T.TreeNode := ⟨v, m + 1, hv⟩
  let i : T.AnchorIndex m := ⟨v', (T.mem_levelNodes _ _).mpr hv⟩
  obtain ⟨w', hsingle⟩ := D.initial_singleton i
  have hw' : w' ∈ (D.stages hU 0).nodes i := by
    change w' ∈ D.initial.nodes i
    rw [hsingle]
    simp
  refine ⟨w'.val, ⟨(D.mem_tailNodes hU 0 _).mpr ⟨i, w', hw', rfl⟩,
    D.anchor_below hU 0 i w' hw'⟩, ?_⟩
  intro w hw
  obtain ⟨j, z, hz, rfl⟩ := (D.mem_tailNodes hU 0 w).mp hw.1
  have hzT : z.val ∈ T.nodes (D.stages hU 0).index := by
    rw [← (D.stages hU 0).height j z hz]
    exact T.nodeHeight_mem z
  have heq : j = i := anchor_eq_of_common_extension j i _ z.val hzT
    (D.anchor_below hU 0 j z hz) hw.2
  subst j
  have hzw' : z = w' := by
    change z ∈ D.initial.nodes i at hz
    rw [hsingle] at hz
    exact Finset.mem_singleton.mp hz
  exact congrArg Subtype.val hzw'

theorem joinedNodes_parent (n : ℕ) (w : α) (hw : w ∈ D.joinedNodes hU (n + 1)) :
    ∃ u ∈ D.joinedNodes hU n, R u w := by
  by_cases hinit : n + 1 ≤ m
  · rw [D.joinedNodes_initial hU (n + 1) hinit] at hw
    obtain ⟨u, ⟨hu, huw⟩, _⟩ := T.ancestor n (n + 1) (Nat.le_succ n) w hw
    exact ⟨u, by rw [D.joinedNodes_initial hU n (by omega)]; exact hu, huw⟩
  · by_cases heq : n = m
    · subst n
      rw [show m + 1 = m + 1 + 0 by omega, D.joinedNodes_tail hU 0] at hw
      obtain ⟨i, z, hz, rfl⟩ := (D.mem_tailNodes hU 0 w).mp hw
      obtain ⟨u, ⟨hu, hui⟩, _⟩ := T.ancestor m (m + 1) (Nat.le_succ m) i.val.val
        ((T.mem_levelNodes _ _).mp i.property)
      exact ⟨u, by rw [D.joinedNodes_initial hU m le_rfl]; exact hu,
        T.rel_trans hui (D.anchor_below hU 0 i z hz)⟩
    · let k := n - m - 1
      have hn : n = m + 1 + k := by dsimp [k]; omega
      rw [hn, show m + 1 + k + 1 = m + 1 + (k + 1) by omega, D.joinedNodes_tail hU (k + 1)] at hw
      rw [hn, D.joinedNodes_tail hU k]
      exact D.tailNodes_parent hU k w hw

theorem joinedNodes_successor (n : ℕ) (u : α) (hu : u ∈ D.joinedNodes hU n)
    (v : α) (hv : v ∈ T.nodes (D.joinedIndex hU n + 1)) (huv : R u v) :
    ∃! w, w ∈ D.joinedNodes hU (n + 1) ∧ R v w := by
  by_cases hinit : n + 1 ≤ m
  · rw [D.joinedIndex_initial hU n (by omega)] at hv
    rw [D.joinedNodes_initial hU (n + 1) hinit]
    refine ⟨v, ⟨hv, T.rel_refl v⟩, ?_⟩
    intro w hw
    exact T.node_eq_of_common_extension (n + 1) (n + 1) w v w hw.1 hv hw.1 (T.rel_refl w) hw.2
  · by_cases heq : n = m
    · subst n
      rw [D.joinedNodes_initial hU m le_rfl] at hu
      rw [D.joinedIndex_initial hU m le_rfl] at hv
      rw [show m + 1 = m + 1 + 0 by omega, D.joinedNodes_tail hU 0]
      exact D.boundary_successor hU v hv
    · let k := n - m - 1
      have hn : n = m + 1 + k := by dsimp [k]; omega
      rw [hn, D.joinedNodes_tail hU k] at hu
      rw [hn, D.joinedIndex_tail hU k] at hv
      rw [hn, show m + 1 + k + 1 = m + 1 + (k + 1) by omega, D.joinedNodes_tail hU (k + 1)]
      exact D.tailNodes_successor hU k u hu v hv huv

noncomputable def strongFrame : T.StrongFrame where
  index := D.joinedIndex hU
  index_strictMono := D.joinedIndex_strictMono hU
  nodes := D.joinedNodes hU
  root := T.root
  nodes_zero := by rw [D.joinedNodes_initial hU 0 (Nat.zero_le m), T.nodes_zero]
  nodes_subset := D.joinedNodes_subset hU
  parent := D.joinedNodes_parent hU
  successor := D.joinedNodes_successor hU

theorem color_stable (u : α) (hu : u ∈ D.joinedNodes hU (m + 1))
    (n : ℕ) (hn : m < n) (v : α) (hv : v ∈ D.joinedNodes hU n) (huv : R u v) :
    c u = c v := by
  rw [show m + 1 = m + 1 + 0 by omega, D.joinedNodes_tail hU 0] at hu
  obtain ⟨i, u', hu', rfl⟩ := (D.mem_tailNodes hU 0 u).mp hu
  let k := n - m - 1
  have heq : n = m + 1 + k := by dsimp [k]; omega
  rw [heq, D.joinedNodes_tail hU k] at hv
  obtain ⟨j, v', hv', rfl⟩ := (D.mem_tailNodes hU k v).mp hv
  have hvT : v'.val ∈ T.nodes (D.stages hU k).index := by
    rw [← (D.stages hU k).height j v' hv']
    exact T.nodeHeight_mem v'
  have hij : j = i := anchor_eq_of_common_extension j i _ v'.val hvT
    (D.anchor_below hU k j v' hv') (T.rel_trans (D.anchor_below hU 0 i u' hu') huv)
  subst j
  exact ((D.stages hU 0).colored i u' hu').trans ((D.stages hU k).colored i v' hv').symm

end TailData

/-- One finite coloring is stabilized above every successor cone after a
prescribed finite prefix, while all levels and nodes of the prefix remain
the actual original ones. There is no Ramsey-oracle premise. -/
theorem tail_stabilization_exists (c : α → K) (m : ℕ) :
    ∃ F : T.StrongFrame,
      (∀ n ≤ m, F.index n = n ∧ F.nodes n = T.nodes n) ∧
      ∀ u ∈ F.nodes (m + 1), ∀ n > m, ∀ v ∈ F.nodes n, R u v → c u = c v := by
  classical
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨D⟩ := T.tailData_exists c U hU m
  refine ⟨D.strongFrame hU, ?_, ?_⟩
  · intro n hn
    exact ⟨D.joinedIndex_initial hU n hn, D.joinedNodes_initial hU n hn⟩
  · intro u hu n hn v hv huv
    exact D.color_stable hU u hu n hn v hv huv

end Generic3Ramsey.SourceTrees.FiniteLevelTree
