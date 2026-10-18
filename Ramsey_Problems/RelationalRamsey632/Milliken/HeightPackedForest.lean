import RelationalRamsey632.Milliken.HeightCanonicalAPI
import RelationalRamsey632.Milliken.PrefixForestGraft
import RelationalRamsey632.Milliken.VectorTailFusion

/-! Neutral full-frontier forests and their actual prefix-preserving graft. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
variable (F : SynchronizedFrame T) (k : ℕ)

abbrev FrontierForest := StrongForest (fun i (a : ConeAnchor (F.frames i).toTree (k + 1)) =>
  coneTree (F.frames i).toTree (k + 1) a)

noncomputable def graftedNativeFrame (B : FrontierForest T F k) :
    SynchronizedFrame (fun i => (F.frames i).toTree) where
  index := PrefixForestGraft.index k B.index
  index_strictMono := PrefixForestGraft.index_strictMono k B.index B.index_strictMono
  frames i := PrefixForestGraft.frame (F.frames i).toTree k B.index B.index_strictMono
    (B.frames i) (B.frame_index i)
  frame_index _ := rfl

noncomputable def forestRefinement (B : FrontierForest T F k) : FrameRefinement T F where
  frame := F.comp (graftedNativeFrame T F k B)
  selector := (graftedNativeFrame T F k B).index
  selector_strictMono := (graftedNativeFrame T F k B).index_strictMono
  index_eq := rfl
  subset i n := SynchronizedFrame.comp_nodes_subset F (graftedNativeFrame T F k B) i n

theorem forestRefinement_preserves (B : FrontierForest T F k) :
    (forestRefinement T F k B).Preserves k := by
  intro n hn
  refine ⟨PrefixForestGraft.index_initial k B.index n hn, ?_⟩
  intro i
  exact (PrefixForestGraft.frame_preserved (F.frames i).toTree k B.index B.index_strictMono
    (B.frames i) (B.frame_index i) n hn).2

theorem forestRefinement_tail_index (B : FrontierForest T F k) (r : ℕ) :
    (forestRefinement T F k B).selector (k + 1 + r) = k + 1 + B.index r :=
  PrefixForestGraft.index_tail k B.index r

theorem forestRefinement_tail_nodes (B : FrontierForest T F k) (i : I) (r : ℕ) :
    (((forestRefinement T F k B).frame).frames i).nodes (k + 1 + r) =
      Finset.univ.biUnion (fun a => (B.frames i a).nodes r) :=
  PrefixForestGraft.nodes_tail (F.frames i).toTree k (B.frames i) r

theorem forest_nodes_level (B : FrontierForest T F k) (i : I)
    (a : ConeAnchor (F.frames i).toTree (k + 1)) (r : ℕ) :
    (B.frames i a).nodes r ⊆ (F.frames i).nodes (k + 1 + B.index r) := by
  intro x hx
  have h := (B.frames i a).nodes_subset r hx
  rw [B.frame_index] at h
  exact coneTree_nodes_subset (F.frames i).toTree (k + 1) a (B.index r) h

theorem forest_nodes_cone (B : FrontierForest T F k) (i : I)
    (a : ConeAnchor (F.frames i).toTree (k + 1)) (r : ℕ) {x : α i}
    (hx : x ∈ (B.frames i a).nodes r) : R i a.val x :=
  coneTree_below (F.frames i).toTree (k + 1) a ((B.frames i a).index r) x
    ((B.frames i a).nodes_subset r hx)

end RelationalRamsey632.Milliken
