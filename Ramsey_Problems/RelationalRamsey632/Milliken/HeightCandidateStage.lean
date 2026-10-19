import RelationalRamsey632.Milliken.HeightStageData
import RelationalRamsey632.Milliken.HeightPackedForest

/-! Recover every actual candidate's selected end levels and its genuine
current-tree prefix. This prevents packed colors from covering only a
chosen subfamily of last-level extensions. -/

namespace RelationalRamsey632.Milliken.HeightCandidateStage

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

theorem core_level_nonempty {h : ℕ} (C : RealizedTreeCore T h) (i : I) (n : Fin h) :
    (C.val i n).Nonempty := by
  obtain ⟨F, hF⟩ := C.property
  have he : (F.frames i).nodes n.val = C.val i n := congrFun (congrFun hF i) n
  rw [← he]
  exact (F.frames i).toTree.nodes_nonempty n.val

theorem selector_prefix_end [Nonempty I] (F : SynchronizedFrame T) (k : ℕ)
    {h : ℕ} (hh : 0 < h) (P : EndedCore T F k h) (G : FrameRefinement T F)
    (hpres : G.Preserves k) (C : RealizedTreeCore T (h + 1))
    (hprefix : prefixCore T C = P.val)
    (l : ℕ → ℕ) (_hl : StrictMono l)
    (hsub : ∀ i (n : Fin (h + 1)), C.val i n ⊆ (G.frame.frames i).nodes (l n.val)) :
    l (h - 1) = k := by
  classical
  let i := Classical.choice (inferInstance : Nonempty I)
  let n : Fin h := ⟨h - 1, by omega⟩
  obtain ⟨w, hw⟩ := core_level_nonempty T P.val i n
  have heq : C.val i n.castSucc = P.val.val i n :=
    congrFun (congrFun (congrArg Subtype.val hprefix) i) n
  have hwC : w ∈ C.val i n.castSucc := heq.symm ▸ hw
  have hwG := hsub i n.castSucc hwC
  have hwFnew := G.subset i (l (h - 1)) hwG
  have hwFold : w ∈ (F.frames i).nodes k := by
    have hw' := (Classical.choose_spec P.property).2.2 i n hw
    change w ∈ (F.frames i).nodes (endedSelector T F k P (h - 1)) at hw'
    rw [endedSelector_last] at hw'
    exact hw'
  have hp0 := (F.frames i).nodes_subset k hwFold
  have hp1 := (F.frames i).nodes_subset (G.selector (l (h - 1))) hwFnew
  rw [F.frame_index] at hp0 hp1
  have hlevel := (T i).level_unique _ _ w hp0 hp1
  have hsel := F.index_strictMono.injective hlevel
  have hfix := (hpres k le_rfl).1
  exact G.selector_strictMono.injective (hsel.symm.trans hfix.symm)

theorem candidate_native_prefix [Nonempty I] (F : SynchronizedFrame T) (k : ℕ)
    {h : ℕ} (hh : 0 < h) (P : EndedCore T F k h) (B : FrontierForest T F k)
    (C : RealizedTreeCore T (h + 1))
    (hC : RelativeCore T (forestRefinement T F k B).frame C)
    (hprefix : prefixCore T C = P.val) :
    ∃ r : ℕ, ∃ f : ℕ → ℕ, ∃ _hf : StrictMono f,
      ∃ Q : ∀ i, FiniteStrongPrefix (F.frames i).toTree f (h + 1),
        f (h - 1) = k ∧ f h = k + 1 + B.index r ∧
        (∀ i n, n < h → (Q i).nodes n = (endedPrefix T F k P i).nodes n) ∧
        (∀ i, (Q i).nodes h = C.val i (Fin.last h)) ∧
        (∀ i, (Q i).nodes h ⊆ Finset.univ.biUnion (fun a => (B.frames i a).nodes r)) := by
  classical
  obtain ⟨l, hl, hsub⟩ := hC
  let G := forestRefinement T F k B
  have hlast : l (h - 1) = k := selector_prefix_end T F k hh P G
    (forestRefinement_preserves T F k B) C hprefix l hl hsub
  have hlh : k < l h := by
    have hd := hl (show h - 1 < h by omega)
    rwa [hlast] at hd
  let r := l h - k - 1
  have hend : l h = k + 1 + r := by dsimp only [r]; omega
  let f := G.selector ∘ l
  have hf : StrictMono f := G.selector_strictMono.comp hl
  let H := Classical.choose C.property
  have hH : H.core (h + 1) = C.val := Classical.choose_spec C.property
  have hHsub : ∀ i n, n < h + 1 → (H.frames i).nodes n ⊆ (F.frames i).nodes (f n) := by
    intro i n hn w hw
    have he : (H.frames i).nodes n = C.val i ⟨n, hn⟩ := congrFun (congrFun hH i) ⟨n, hn⟩
    have hwG := hsub i ⟨n, hn⟩ (he ▸ hw)
    exact G.subset i (l n) hwG
  let Q : ∀ i, FiniteStrongPrefix (F.frames i).toTree f (h + 1) :=
    fun i => relativeFinitePrefix (F.frames i) (H.frames i) f hf (h + 1) (hHsub i)
  have hQ : ∀ i (n : Fin (h + 1)), (Q i).nodes n.val = C.val i n :=
    fun i n => congrFun (congrFun hH i) n
  refine ⟨r, f, hf, Q, ?_, ?_, ?_, ?_, ?_⟩
  · change G.selector (l (h - 1)) = k
    rw [hlast]
    exact ((forestRefinement_preserves T F k B) k le_rfl).1
  · change G.selector (l h) = k + 1 + B.index r
    rw [hend]
    exact forestRefinement_tail_index T F k B r
  · intro i n hn
    have hc : C.val i (⟨n, by omega⟩ : Fin (h + 1)) = P.val.val i ⟨n, hn⟩ :=
      congrFun (congrFun (congrArg Subtype.val hprefix) i) ⟨n, hn⟩
    exact (hQ i ⟨n, by omega⟩).trans
      (hc.trans (endedPrefix_core T F k P i ⟨n, hn⟩).symm)
  · intro i
    exact hQ i (Fin.last h)
  · intro i w hw
    have hwC : w ∈ C.val i (Fin.last h) := (hQ i (Fin.last h)) ▸ hw
    have hwG := hsub i (Fin.last h) hwC
    change w ∈ (G.frame.frames i).nodes (l h) at hwG
    rw [hend, forestRefinement_tail_nodes] at hwG
    exact hwG

end RelationalRamsey632.Milliken.HeightCandidateStage
