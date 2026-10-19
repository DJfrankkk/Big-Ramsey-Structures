import RelationalRamsey632.Milliken.HeightHLTransport
import RelationalRamsey632.Milliken.ConeTrees

/-! The exact height-one strong-core Ramsey theorem, derived from proved HL. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}

noncomputable def coneFrame (T : FiniteLevelTree α R) (b : ℕ) (a : ConeAnchor T b) :
    T.StrongFrame where
  index n := b + n
  index_strictMono := fun _ _ h => Nat.add_lt_add_left h b
  nodes := (coneTree T b a).nodes
  root := a.val
  nodes_zero := (coneTree T b a).nodes_zero
  nodes_subset n := coneTree_nodes_subset T b a n
  parent := (StrongFrame.identity (coneTree T b a)).parent
  successor := by
    intro n u hu v hv huv
    have hav : R a.val v := T.rel_trans (coneTree_below T b a n u hu) huv
    have hvc : v ∈ (coneTree T b a).nodes (n + 1) :=
      (mem_coneNodes T b a (n + 1) v).mpr ⟨by simpa only [Nat.add_assoc] using hv, hav⟩
    refine ⟨v, ⟨hvc, T.rel_refl v⟩, ?_⟩
    intro w hw
    exact T.node_eq_of_common_extension _ _ w v w
      (coneTree_nodes_subset T b a (n + 1) hw.1) hv
      (coneTree_nodes_subset T b a (n + 1) hw.1) (T.rel_refl w) hw.2

variable {I : Type} {αs : I → Type} [∀ i, DecidableEq (αs i)]
variable {Rs : ∀ i, αs i → αs i → Prop} (T : ∀ i, FiniteLevelTree (αs i) (Rs i))

noncomputable def rootedFrame (b : ℕ) (x : VectorNode T)
    (hx : ∀ i, (T i).nodeHeight (x i) = b) : SynchronizedFrame T where
  index n := b + n
  index_strictMono := fun _ _ h => Nat.add_lt_add_left h b
  frames i := coneFrame (T i) b ⟨(x i).val, hx i ▸ (T i).nodeHeight_mem (x i)⟩
  frame_index _ := rfl

noncomputable def rootCore (b : ℕ) (x : VectorNode T)
    (hx : ∀ i, (T i).nodeHeight (x i) = b) : RealizedTreeCore T 1 :=
  (rootedFrame T b x hx).realizedCore 1

theorem rootCore_level (b : ℕ) (x : VectorNode T)
    (hx : ∀ i, (T i).nodeHeight (x i) = b) (i : I) (j : Fin 1) :
    (rootCore T b x hx).val i j = {(x i).val} := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact (coneTree (T i) b ⟨(x i).val, hx i ▸ (T i).nodeHeight_mem (x i)⟩).nodes_zero

noncomputable def heightOneColor {K : Type} (c : RealizedTreeCore T 1 → K) (x : VectorNode T) : K := by
  classical
  exact if hx : ∃ b, ∀ i, (T i).nodeHeight (x i) = b then
    c (rootCore T (Classical.choose hx) x (Classical.choose_spec hx))
  else c ((SynchronizedFrame.identity : SynchronizedFrame T).realizedCore 1)

theorem heightOneColor_aligned {K : Type} (c : RealizedTreeCore T 1 → K)
    (b : ℕ) (x : VectorNode T) (hx : ∀ i, (T i).nodeHeight (x i) = b) :
    heightOneColor T c x = c (rootCore T b x hx) := by
  classical
  rw [heightOneColor, dif_pos (show ∃ b, ∀ i, (T i).nodeHeight (x i) = b from ⟨b, hx⟩)]
  apply congrArg c
  apply Subtype.ext
  funext i j
  simp only [rootCore_level]

theorem height_one [Fintype I] (K : Type) [Fintype K] : MillikenHeight T 1 K := by
  classical
  intro c
  obtain ⟨H⟩ := strong_subtree_ramsey_fintype T K (heightOneColor T c)
  let F := H.toSynchronizedFrame
  refine ⟨F, H.color, ?_⟩
  intro C hC
  obtain ⟨l, _, hsub⟩ := hC
  obtain ⟨G, hG⟩ := C.property
  let x : VectorNode T := fun i =>
    ⟨(G.frames i).root, G.index 0, by
      rw [← G.frame_index i]
      apply (G.frames i).nodes_subset 0
      rw [(G.frames i).nodes_zero]
      exact Finset.mem_singleton_self _⟩
  have hx : ∀ i, (x i).val ∈ (H.frames i).nodes (l 0) := by
    intro i
    apply hsub i 0
    rw [← hG]
    change (G.frames i).root ∈ (G.frames i).nodes 0
    rw [(G.frames i).nodes_zero]
    exact Finset.mem_singleton_self _
  have haligned : ∀ i, (T i).nodeHeight (x i) = H.index (l 0) := by
    intro i
    apply (T i).nodeHeight_eq
    rw [← H.frame_index i]
    exact (H.frames i).nodes_subset (l 0) (hx i)
  have heCore : rootCore T (H.index (l 0)) x haligned = C := by
    apply Subtype.ext
    funext i j
    rw [rootCore_level, ← hG]
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact (G.frames i).nodes_zero.symm
  have hc := H.colored (l 0) x hx
  rw [heightOneColor_aligned T c (H.index (l 0)) x haligned, heCore] at hc
  exact hc

end RelationalRamsey632.Milliken
