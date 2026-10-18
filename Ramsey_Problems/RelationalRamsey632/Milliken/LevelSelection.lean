import RelationalRamsey632.Milliken.VectorMatrices

/-! Genuine strong-subtree completion on any prescribed infinite level set. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    (T : FiniteLevelTree α R)

noncomputable def levelLift (n m : ℕ) (hnm : n ≤ m) (v : α) : α := by
  classical
  exact if hv : v ∈ T.nodes n then Classical.choose (T.extend n m hnm v hv) else T.root

theorem levelLift_mem (n m : ℕ) (hnm : n ≤ m) (v : α) (hv : v ∈ T.nodes n) :
    levelLift T n m hnm v ∈ T.nodes m := by
  classical
  simp only [levelLift, dif_pos hv]
  exact (Classical.choose_spec (T.extend n m hnm v hv)).1

theorem levelLift_extends (n m : ℕ) (hnm : n ≤ m) (v : α) (hv : v ∈ T.nodes n) :
    R v (levelLift T n m hnm v) := by
  classical
  simp only [levelLift, dif_pos hv]
  exact (Classical.choose_spec (T.extend n m hnm v hv)).2

theorem levelLift_injective (n m : ℕ) (hnm : n ≤ m) :
    Set.InjOn (levelLift T n m hnm) (T.nodes n) := by
  intro v hv w hw heq
  exact T.node_eq_of_common_extension n m v w (levelLift T n m hnm v)
    hv hw (levelLift_mem T n m hnm v hv)
    (levelLift_extends T n m hnm v hv)
    (heq.symm ▸ levelLift_extends T n m hnm w hw)

namespace LevelSelection

variable (index : ℕ → ℕ) (hm : StrictMono index)

noncomputable def root : α := (T.nodes_nonempty (index 0)).choose

theorem root_mem : root T index ∈ T.nodes (index 0) :=
  (T.nodes_nonempty (index 0)).choose_spec

noncomputable def successors (n : ℕ) (F : Finset α) : Finset α := by
  classical
  exact (T.nodes (index n + 1)).filter (fun v => ∃ u ∈ F, R u v)

noncomputable def nodes : ℕ → Finset α
  | 0 => {root T index}
  | n + 1 =>
      (successors T index n (nodes n)).image
        (levelLift T (index n + 1) (index (n + 1))
          (Nat.succ_le_of_lt (hm (Nat.lt_succ_self n))))

theorem nodes_subset (n : ℕ) : nodes T index hm n ⊆ T.nodes (index n) := by
  classical
  cases n with
  | zero =>
    intro u hu
    have heq : u = root T index := Finset.mem_singleton.mp hu
    exact heq ▸ root_mem T index
  | succ n =>
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact levelLift_mem T _ _ _ v (Finset.mem_filter.mp hv).1

theorem parent (n : ℕ) (w : α) (hw : w ∈ nodes T index hm (n + 1)) :
    ∃ u ∈ nodes T index hm n, R u w := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hv, u, hu, huv⟩ := Finset.mem_filter.mp hv
  exact ⟨u, hu, T.rel_trans huv (levelLift_extends T _ _ _ v hv)⟩

theorem successor (n : ℕ) (u : α) (hu : u ∈ nodes T index hm n)
    (v : α) (hv : v ∈ T.nodes (index n + 1)) (huv : R u v) :
    ∃! w, w ∈ nodes T index hm (n + 1) ∧ R v w := by
  classical
  let lift := levelLift T (index n + 1) (index (n + 1))
    (Nat.succ_le_of_lt (hm (Nat.lt_succ_self n)))
  have hvSucc : v ∈ successors T index n (nodes T index hm n) :=
    Finset.mem_filter.mpr ⟨hv, u, hu, huv⟩
  refine ⟨lift v, ⟨Finset.mem_image.mpr ⟨v, hvSucc, rfl⟩,
    levelLift_extends T _ _ _ v hv⟩, ?_⟩
  intro w hw
  obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hw.1
  have hvlevel := (Finset.mem_filter.mp hv').1
  have hvv' : v = v' :=
    T.node_eq_of_common_extension _ _ v v' (lift v')
      hv hvlevel (levelLift_mem T _ _ _ v' hvlevel) hw.2
      (levelLift_extends T _ _ _ v' hvlevel)
  exact congrArg lift hvv'.symm

noncomputable def frame : T.StrongFrame where
  index := index
  index_strictMono := hm
  nodes := nodes T index hm
  root := root T index
  nodes_zero := rfl
  nodes_subset := nodes_subset T index hm
  parent := parent T index hm
  successor := successor T index hm

@[simp] theorem frame_index : (frame T index hm).index = index := rfl

end LevelSelection

end RelationalRamsey632.Milliken
