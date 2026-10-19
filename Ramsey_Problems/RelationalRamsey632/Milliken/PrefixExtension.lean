import RelationalRamsey632.Milliken.LevelSelection

/-! Every finite strong prefix extends on a prescribed common infinite
level sequence. No extension oracle is used. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    (T : FiniteLevelTree α R) (e : ℕ → ℕ) (he : StrictMono e) (h : ℕ)

structure FiniteStrongPrefix where
  index_strictMono : StrictMono e
  nodes : ℕ → Finset α
  root : α
  nodes_zero : nodes 0 = {root}
  nodes_subset : ∀ n, n < h → nodes n ⊆ T.nodes (e n)
  parent : ∀ n, n + 1 < h → ∀ w ∈ nodes (n + 1), ∃ u ∈ nodes n, R u w
  successor : ∀ n, n + 1 < h → ∀ u ∈ nodes n,
    ∀ v ∈ T.nodes (e n + 1), R u v →
      ∃! w, w ∈ nodes (n + 1) ∧ R v w

namespace FiniteStrongPrefix

variable {T e he h} (P : FiniteStrongPrefix T e h)

noncomputable def completedNext (n : ℕ) (F : Finset α) : Finset α :=
  (LevelSelection.successors T e n F).image
    (levelLift T (e n + 1) (e (n + 1))
      (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))))

theorem completedNext_subset (n : ℕ) (F : Finset α) :
    completedNext (T := T) (e := e) (he := he) n F ⊆ T.nodes (e (n + 1)) := by
  classical
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  exact levelLift_mem T _ _ _ v (Finset.mem_filter.mp hv).1

theorem completedNext_parent (n : ℕ) (F : Finset α) (w : α)
    (hw : w ∈ completedNext (T := T) (e := e) (he := he) n F) :
    ∃ u ∈ F, R u w := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hv, u, hu, huv⟩ := Finset.mem_filter.mp hv
  exact ⟨u, hu, T.rel_trans huv (levelLift_extends T _ _ _ v hv)⟩

theorem completedNext_successor (n : ℕ) (F : Finset α)
    (u : α) (hu : u ∈ F) (v : α) (hv : v ∈ T.nodes (e n + 1)) (huv : R u v) :
    ∃! w, w ∈ completedNext (T := T) (e := e) (he := he) n F ∧ R v w := by
  classical
  let lift := levelLift T (e n + 1) (e (n + 1))
    (Nat.succ_le_of_lt (he (Nat.lt_succ_self n)))
  refine ⟨lift v, ⟨?_, levelLift_extends T _ _ _ v hv⟩, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨v, Finset.mem_filter.mpr ⟨hv, u, hu, huv⟩, rfl⟩
  · intro w hw
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hw.1
    have hvlevel := (Finset.mem_filter.mp hv').1
    have hvv' : v = v' := T.node_eq_of_common_extension _ _ v v' (lift v')
      hv hvlevel (levelLift_mem T _ _ _ v' hvlevel) hw.2
      (levelLift_extends T _ _ _ v' hvlevel)
    exact congrArg lift hvv'.symm

noncomputable def extensionNodes : ℕ → Finset α
  | 0 => {P.root}
  | n + 1 => if n + 1 < h then P.nodes (n + 1) else
      completedNext (T := T) (e := e) (he := P.index_strictMono) n (extensionNodes n)

theorem extensionNodes_initial (n : ℕ) (hn : n < h) :
    P.extensionNodes n = P.nodes n := by
  cases n with
  | zero => exact P.nodes_zero.symm
  | succ n => simp only [extensionNodes, if_pos hn]

theorem extensionNodes_subset (hh : 0 < h) (n : ℕ) :
    P.extensionNodes n ⊆ T.nodes (e n) := by
  cases n with
  | zero =>
    rw [P.extensionNodes_initial 0 hh]
    exact P.nodes_subset 0 hh
  | succ n =>
    by_cases hn : n + 1 < h
    · rw [P.extensionNodes_initial (n + 1) hn]
      exact P.nodes_subset (n + 1) hn
    · simp only [extensionNodes, if_neg hn]
      exact completedNext_subset (he := P.index_strictMono) n _

theorem extension_parent (n : ℕ) (w : α) (hw : w ∈ P.extensionNodes (n + 1)) :
    ∃ u ∈ P.extensionNodes n, R u w := by
  by_cases hn : n + 1 < h
  · rw [P.extensionNodes_initial (n + 1) hn] at hw
    obtain ⟨u, hu, huw⟩ := P.parent n hn w hw
    exact ⟨u, by rw [P.extensionNodes_initial n (by omega)]; exact hu, huw⟩
  · simp only [extensionNodes, if_neg hn] at hw
    exact completedNext_parent (he := P.index_strictMono) n _ w hw

theorem extension_successor (n : ℕ) (u : α) (hu : u ∈ P.extensionNodes n)
    (v : α) (hv : v ∈ T.nodes (e n + 1)) (huv : R u v) :
    ∃! w, w ∈ P.extensionNodes (n + 1) ∧ R v w := by
  by_cases hn : n + 1 < h
  · rw [P.extensionNodes_initial n (by omega)] at hu
    rw [P.extensionNodes_initial (n + 1) hn]
    exact P.successor n hn u hu v hv huv
  · simp only [extensionNodes, if_neg hn]
    exact completedNext_successor (he := P.index_strictMono) n _ u hu v hv huv

noncomputable def extend (hh : 0 < h) : T.StrongFrame where
  index := e
  index_strictMono := P.index_strictMono
  nodes := P.extensionNodes
  root := P.root
  nodes_zero := rfl
  nodes_subset := P.extensionNodes_subset hh
  parent := P.extension_parent
  successor := P.extension_successor

theorem extend_initial (hh : 0 < h) (n : ℕ) (hn : n < h) :
    (P.extend hh).nodes n = P.nodes n := P.extensionNodes_initial n hn

@[simp] theorem extend_index (hh : 0 < h) : (P.extend hh).index = e := rfl

end FiniteStrongPrefix

end RelationalRamsey632.Milliken
