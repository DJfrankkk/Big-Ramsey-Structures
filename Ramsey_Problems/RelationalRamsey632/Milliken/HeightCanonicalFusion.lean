import RelationalRamsey632.Milliken.HeightCanonicalAPI

/-! Diagonal fusion of actual root-preserving finite-prefix canonicalization
steps. Only prefixes ending at the current cut are processed. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

namespace HeightCanonicalFusion

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop}
    (T : ∀ i, FiniteLevelTree (α i) (R i))
    {h : ℕ} {K : Type} (c : RealizedTreeCore T (h + 1) → K)
    (hcanon : CanonicalStep T c)

noncomputable def step (F : SynchronizedFrame T) (k : ℕ) : FrameRefinement T F :=
  Classical.choose (hcanon F k)

theorem step_preserves (F : SynchronizedFrame T) (k : ℕ) :
    (step T c hcanon F k).Preserves k := (Classical.choose_spec (hcanon F k)).1

theorem step_canonical (F : SynchronizedFrame T) (k : ℕ) (P : RealizedTreeCore T h)
    (hP : EndsAt T F k P) :
    EndHomogeneous T c (step T c hcanon F k).frame P :=
  (Classical.choose_spec (hcanon F k)).2 P hP

noncomputable def stages : ℕ → SynchronizedFrame T
  | 0 => SynchronizedFrame.identity
  | k + 1 => (step T c hcanon (stages k) k).frame

theorem stages_index_step (k n : ℕ) (hn : n ≤ k) :
    (stages T c hcanon (k + 1)).index n = (stages T c hcanon k).index n := by
  have hi := congrFun (step T c hcanon (stages T c hcanon k) k).index_eq n
  change (stages T c hcanon (k + 1)).index n =
    (stages T c hcanon k).index ((step T c hcanon (stages T c hcanon k) k).selector n) at hi
  exact hi.trans (congrArg (stages T c hcanon k).index
    ((step_preserves T c hcanon (stages T c hcanon k) k) n hn).1)

theorem stages_nodes_step (k n : ℕ) (hn : n ≤ k) (i : I) :
    ((stages T c hcanon (k + 1)).frames i).nodes n =
      ((stages T c hcanon k).frames i).nodes n :=
  ((step_preserves T c hcanon (stages T c hcanon k) k) n hn).2 i

theorem stages_index_fixed (n r s : ℕ) (hnr : n ≤ r) (hrs : r ≤ s) :
    (stages T c hcanon s).index n = (stages T c hcanon r).index n := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih => exact (stages_index_step T c hcanon s n (hnr.trans hrs)).trans ih

theorem stages_nodes_fixed (n r s : ℕ) (hnr : n ≤ r) (hrs : r ≤ s) (i : I) :
    ((stages T c hcanon s).frames i).nodes n = ((stages T c hcanon r).frames i).nodes n := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih => exact (stages_nodes_step T c hcanon s n (hnr.trans hrs) i).trans ih

theorem earlier_data (r s : ℕ) (hrs : r ≤ s) (n : ℕ) :
    ∃ j ≥ n, (stages T c hcanon s).index n = (stages T c hcanon r).index j ∧
      ∀ i, ((stages T c hcanon s).frames i).nodes n ⊆
        ((stages T c hcanon r).frames i).nodes j := by
  induction s, hrs using Nat.le_induction generalizing n with
  | base => exact ⟨n, le_rfl, rfl, fun _ => Finset.Subset.refl _⟩
  | succ s hrs ih =>
    let S := step T c hcanon (stages T c hcanon s) s
    obtain ⟨j, hj, hindex, hsub⟩ := ih (S.selector n)
    have hnew : (stages T c hcanon (s + 1)).index n =
        (stages T c hcanon s).index (S.selector n) := congrFun S.index_eq n
    exact ⟨j, (S.selector_strictMono.id_le n).trans hj, hnew.trans hindex,
      fun i => (S.subset i n).trans (hsub i)⟩

noncomputable def fusionIndex (n : ℕ) : ℕ := (stages T c hcanon n).index n

theorem fusionIndex_strictMono : StrictMono (fusionIndex T c hcanon) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (stages T c hcanon n).index n < (stages T c hcanon (n + 1)).index (n + 1)
  rw [← stages_index_step T c hcanon n n le_rfl]
  exact (stages T c hcanon (n + 1)).index_strictMono (Nat.lt_succ_self n)

noncomputable def fusionFrames (i : I) : (T i).StrongFrame where
  index := fusionIndex T c hcanon
  index_strictMono := fusionIndex_strictMono T c hcanon
  nodes := fun n => ((stages T c hcanon n).frames i).nodes n
  root := (T i).root
  nodes_zero := (T i).nodes_zero
  nodes_subset n := by
    have h := ((stages T c hcanon n).frames i).nodes_subset n
    rw [(stages T c hcanon n).frame_index i] at h
    exact h
  parent := by
    intro n w hw
    obtain ⟨u, hu, huw⟩ := ((stages T c hcanon (n + 1)).frames i).parent n w hw
    rw [stages_nodes_step T c hcanon n n le_rfl i] at hu
    exact ⟨u, hu, huw⟩
  successor := by
    intro n u hu v hv huv
    have hu' : u ∈ ((stages T c hcanon (n + 1)).frames i).nodes n := by
      rw [stages_nodes_step T c hcanon n n le_rfl i]
      exact hu
    have hv' : v ∈ (T i).nodes (((stages T c hcanon (n + 1)).frames i).index n + 1) := by
      rw [(stages T c hcanon (n + 1)).frame_index i,
        stages_index_step T c hcanon n n le_rfl]
      exact hv
    exact ((stages T c hcanon (n + 1)).frames i).successor n u hu' v hv' huv

noncomputable def fusion : SynchronizedFrame T :=
  ⟨fusionIndex T c hcanon, fusionIndex_strictMono T c hcanon, fusionFrames T c hcanon, fun _ => rfl⟩

theorem fusion_nodes_fixed (r n : ℕ) (hnr : n ≤ r) (i : I) :
    ((fusion T c hcanon).frames i).nodes n = ((stages T c hcanon r).frames i).nodes n :=
  (stages_nodes_fixed T c hcanon n n r le_rfl hnr i).symm

theorem fusion_earlier_data (r n : ℕ) :
    ∃ j ≥ n, (fusion T c hcanon).index n = (stages T c hcanon r).index j ∧
      ∀ i, ((fusion T c hcanon).frames i).nodes n ⊆
        ((stages T c hcanon r).frames i).nodes j := by
  by_cases hrn : r ≤ n
  · exact earlier_data T c hcanon r n hrn n
  · have hnr : n ≤ r := by omega
    refine ⟨n, le_rfl, (stages_index_fixed T c hcanon n n r le_rfl hnr).symm, ?_⟩
    intro i
    rw [fusion_nodes_fixed T c hcanon r n hnr i]

noncomputable def earlierSelector (r n : ℕ) : ℕ :=
  Classical.choose (fusion_earlier_data T c hcanon r n)

theorem earlierSelector_index (r n : ℕ) :
    (fusion T c hcanon).index n = (stages T c hcanon r).index (earlierSelector T c hcanon r n) :=
  (Classical.choose_spec (fusion_earlier_data T c hcanon r n)).2.1

theorem earlierSelector_strictMono (r : ℕ) : StrictMono (earlierSelector T c hcanon r) := by
  intro n m hnm
  apply (stages T c hcanon r).index_strictMono.lt_iff_lt.mp
  rw [← earlierSelector_index, ← earlierSelector_index]
  exact (fusion T c hcanon).index_strictMono hnm

noncomputable def fusionRefinement (r : ℕ) : FrameRefinement T (stages T c hcanon r) where
  frame := fusion T c hcanon
  selector := earlierSelector T c hcanon r
  selector_strictMono := earlierSelector_strictMono T c hcanon r
  index_eq := funext (earlierSelector_index T c hcanon r)
  subset i n := (Classical.choose_spec (fusion_earlier_data T c hcanon r n)).2.2 i

theorem fusion_endHomogeneous (hh : 0 < h) (P : RealizedTreeCore T h)
    (hP : RelativeCore T (fusion T c hcanon) P) :
    EndHomogeneous T c (fusion T c hcanon) P := by
  obtain ⟨l, hl, hsub⟩ := hP
  let k := l (h - 1)
  have hEnds : EndsAt T (stages T c hcanon k) k P := by
    refine ⟨l, hl, rfl, ?_⟩
    intro i n
    have hnk : l n.val ≤ k := hl.monotone (by have hn := n.isLt; omega)
    rw [← fusion_nodes_fixed T c hcanon k (l n.val) hnk i]
    exact hsub i n
  have hhom := step_canonical T c hcanon (stages T c hcanon k) k P hEnds
  exact endHomogeneous_refinement T (fusionRefinement T c hcanon (k + 1)) hhom

end HeightCanonicalFusion

theorem canonical_fusion {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    {h : ℕ} (hh : 0 < h) {K : Type} (c : RealizedTreeCore T (h + 1) → K)
    (hcanon : CanonicalStep T c) :
    ∃ F : SynchronizedFrame T, ∃ d : RealizedTreeCore T h → K,
      ∀ C : RealizedTreeCore T (h + 1), RelativeCore T F C → c C = d (prefixCore T C) := by
  classical
  let F := HeightCanonicalFusion.fusion T c hcanon
  have hhom : ∀ P : RealizedTreeCore T h, RelativeCore T F P → EndHomogeneous T c F P :=
    HeightCanonicalFusion.fusion_endHomogeneous T c hcanon hh
  let d : RealizedTreeCore T h → K := fun P =>
    if hp : RelativeCore T F P then Classical.choose (hhom P hp) else c (F.realizedCore (h + 1))
  refine ⟨F, d, ?_⟩
  intro C hC
  have hp := relative_prefix T F C hC
  change c C = if hp : RelativeCore T F (prefixCore T C) then _ else _
  rw [dif_pos hp]
  exact Classical.choose_spec (hhom (prefixCore T C) hp) C hC rfl

theorem heightFactorization_of_canonicalSteps {I : Type}
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    {h : ℕ} (hh : 0 < h) {K : Type}
    (hcanon : ∀ c : RealizedTreeCore T (h + 1) → K, CanonicalStep T c) :
    HeightFactorization T h K :=
  fun c => canonical_fusion T hh c (hcanon c)

end RelationalRamsey632.Milliken
