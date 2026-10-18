import Generic3Ramsey.SourceTailStabilization
import Generic3Ramsey.SourceStableSections
import Mathlib.Data.Fintype.Pi

/-! Countable section fusion with one common selected level sequence. -/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree.SectionFusion

variable {α β : Type} [DecidableEq α] [DecidableEq β]
variable {R : α → α → Prop} {Q : β → β → Prop}
variable (S : FiniteLevelTree α R) (T : FiniteLevelTree β Q) (P : α → β → Prop)

def SectionIndex (F : S.StrongFrame) (k : ℕ) := {y : β // y ∈ T.nodes (F.index k)}

noncomputable instance sectionIndex_fintype (F : S.StrongFrame) (k : ℕ) :
    Fintype (SectionIndex S T F k) := by
  classical
  change Fintype {y : β // y ∈ T.nodes (F.index k)}
  infer_instance

structure Step (F : S.StrongFrame) (k : ℕ) where
  subframe : F.toTree.StrongFrame
  preserved : ∀ n ≤ k, subframe.index n = n ∧ subframe.nodes n = F.nodes n
  stable : ∀ y ∈ T.nodes (F.index k), ∀ u ∈ subframe.nodes (k + 1),
    ∀ n > k, ∀ v ∈ subframe.nodes n, R u v → (P u y ↔ P v y)

theorem step_exists (F : S.StrongFrame) (k : ℕ) : Nonempty (Step S T P F k) := by
  classical
  let color := fun u : α => fun y : SectionIndex S T F k => decide (P u y.val)
  obtain ⟨G, hprefix, hstable⟩ := F.toTree.tail_stabilization_exists color k
  refine ⟨⟨G, hprefix, ?_⟩⟩
  intro y hy u hu n hn v hv huv
  have heq := congrArg (fun f => f (⟨y, hy⟩ : SectionIndex S T F k))
    (hstable u hu n hn v hv huv)
  simpa only [color, decide_eq_decide] using heq

noncomputable def step (F : S.StrongFrame) (k : ℕ) : Step S T P F k :=
  Classical.choice (step_exists S T P F k)

noncomputable def frames (source : FiniteLevelTree α R) (target : FiniteLevelTree β Q)
    (pred : α → β → Prop) : ℕ → source.StrongFrame
  | 0 => StrongFrame.identity source
  | k + 1 => (frames source target pred k).comp (step source target pred (frames source target pred k) k).subframe

theorem frames_index_step (k n : ℕ) (hn : n ≤ k) :
    (frames S T P (k + 1)).index n = (frames S T P k).index n := by
  change (frames S T P k).index ((step S T P (frames S T P k) k).subframe.index n) = _
  rw [((step S T P (frames S T P k) k).preserved n hn).1]

theorem frames_nodes_step (k n : ℕ) (hn : n ≤ k) :
    (frames S T P (k + 1)).nodes n = (frames S T P k).nodes n :=
  ((step S T P (frames S T P k) k).preserved n hn).2

theorem frames_index_fixed (n r s : ℕ) (hnr : n ≤ r) (hrs : r ≤ s) :
    (frames S T P s).index n = (frames S T P r).index n := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih => exact (frames_index_step S T P s n (hnr.trans hrs)).trans ih

theorem frames_nodes_fixed (n r s : ℕ) (hnr : n ≤ r) (hrs : r ≤ s) :
    (frames S T P s).nodes n = (frames S T P r).nodes n := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih => exact (frames_nodes_step S T P s n (hnr.trans hrs)).trans ih

/-- Later selected nodes remain in earlier strong trees, at levels whose
indices have not decreased. -/
theorem node_in_earlier (r s : ℕ) (hrs : r ≤ s) :
    ∀ n u, u ∈ (frames S T P s).nodes n →
      ∃ j ≥ n, u ∈ (frames S T P r).nodes j := by
  induction s, hrs using Nat.le_induction with
  | base => intro n u hu; exact ⟨n, le_rfl, hu⟩
  | succ s hrs ih =>
      intro n u hu
      let G := (step S T P (frames S T P s) s).subframe
      have huG : u ∈ G.nodes n := hu
      obtain ⟨j, hj, huj⟩ := ih (G.index n) u (G.nodes_subset n huG)
      exact ⟨j, (G.index_ge n).trans hj, huj⟩

noncomputable def fusion : S.StrongFrame where
  index := fun n => (frames S T P n).index n
  index_strictMono := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [← frames_index_step S T P n n le_rfl]
    exact (frames S T P (n + 1)).index_strictMono (Nat.lt_succ_self n)
  nodes := fun n => (frames S T P n).nodes n
  root := S.root
  nodes_zero := S.nodes_zero
  nodes_subset := fun n => (frames S T P n).nodes_subset n
  parent := by
    intro n w hw
    obtain ⟨u, hu, huw⟩ := (frames S T P (n + 1)).parent n w hw
    rw [frames_nodes_step S T P n n le_rfl] at hu
    exact ⟨u, hu, huw⟩
  successor := by
    intro n u hu v hv huv
    have hu' : u ∈ (frames S T P (n + 1)).nodes n := by
      rw [frames_nodes_step S T P n n le_rfl]
      exact hu
    have hv' : v ∈ S.nodes ((frames S T P (n + 1)).index n + 1) := by
      rw [frames_index_step S T P n n le_rfl]
      exact hv
    exact (frames S T P (n + 1)).successor n u hu' v hv' huv

theorem fusion_index_zero : (fusion S T P).index 0 = 0 := rfl

noncomputable def otherTree : FiniteLevelTree β Q :=
  T.restrictLevels (fusion S T P).index (fusion S T P).index_strictMono (fusion_index_zero S T P)

/-- All sections are stabilized on the fused first tree relative to the
same full-level subsequence in the second tree. -/
theorem fusion_stable_sections : (fusion S T P).toTree.StableSections (otherTree S T P) P := by
  intro u v y hhigh huv
  let n := (fusion S T P).toTree.nodeHeight u
  let l := (fusion S T P).toTree.nodeHeight v
  let k := (otherTree S T P).nodeHeight y
  have hkn : k < n := hhigh
  have hnl : n ≤ l := (fusion S T P).toTree.nodeHeight_le huv
  have huN : u.val ∈ (frames S T P n).nodes n := (fusion S T P).toTree.nodeHeight_mem u
  have hvL : v.val ∈ (frames S T P l).nodes l := (fusion S T P).toTree.nodeHeight_mem v
  have hyK : y.val ∈ T.nodes ((frames S T P k).index k) := (otherTree S T P).nodeHeight_mem y
  obtain ⟨a, ⟨ha, hau⟩, _⟩ := (fusion S T P).ancestor (k + 1) n (by omega) u.val huN
  obtain ⟨j, hj, huj⟩ := node_in_earlier S T P (k + 1) n (by omega) n u.val huN
  obtain ⟨p, hp, hvp⟩ := node_in_earlier S T P (k + 1) l (by omega) l v.val hvL
  let G := step S T P (frames S T P k) k
  have haG : a ∈ G.subframe.nodes (k + 1) := ha
  have huG : u.val ∈ G.subframe.nodes j := huj
  have hvG : v.val ∈ G.subframe.nodes p := hvp
  have hauP := G.stable y.val hyK a haG j (by omega) u.val huG hau
  have havP := G.stable y.val hyK a haG p (by omega) v.val hvG (S.rel_trans hau huv)
  exact hauP.symm.trans havP

end Generic3Ramsey.SourceTrees.FiniteLevelTree.SectionFusion
