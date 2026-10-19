import RelationalRamsey632.Milliken.HeightStageData
import RelationalRamsey632.Milliken.HeightPackedForest
import RelationalRamsey632.Milliken.HeightHLTransport

/-! All-dimensional HL canonizes all ended prefixes on the packed full frontier. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
variable (F : SynchronizedFrame T) (k : ℕ)

abbrev PackedFrontier := (i : I) × ConeAnchor (F.frames i).toTree (k + 1)

noncomputable def frontierTrees (j : PackedFrontier T F k) :
    FiniteLevelTree (α j.1) (R j.1) :=
  coneTree (F.frames j.1).toTree (k + 1) j.2

def frontierLeaves (x : VectorNode (frontierTrees T F k)) :
    ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i :=
  fun i a => (x ⟨i, a⟩).val

theorem frontierLeaves_level (x : VectorNode (frontierTrees T F k)) (m : ℕ)
    (hx : ∀ j, (frontierTrees T F k j).nodeHeight (x j) = m) :
    ∀ i a, frontierLeaves T F k x i a ∈ (F.frames i).nodes (k + 1 + m) := by
  intro i a
  have h := (frontierTrees T F k ⟨i, a⟩).nodeHeight_mem (x ⟨i, a⟩)
  rw [hx] at h
  exact coneTree_nodes_subset (F.frames i).toTree (k + 1) a m h

theorem frontierLeaves_cone (x : VectorNode (frontierTrees T F k)) :
    ∀ i a, R i a.val (frontierLeaves T F k x i a) := by
  intro i a
  exact coneTree_below (F.frames i).toTree (k + 1) a
    ((frontierTrees T F k ⟨i, a⟩).nodeHeight (x ⟨i, a⟩)) (x ⟨i, a⟩).val
    ((frontierTrees T F k ⟨i, a⟩).nodeHeight_mem (x ⟨i, a⟩))

noncomputable def frontierColor {h : ℕ} {K : Type} (c : RealizedTreeCore T (h + 1) → K)
    (hh : 0 < h) (x : VectorNode (frontierTrees T F k)) : EndedCore T F k h → K := by
  classical
  intro P
  exact if hx : ∃ m, ∀ j, (frontierTrees T F k j).nodeHeight (x j) = m then
    c (appendEndedCore T F k P hh (k + 1 + Classical.choose hx) (frontierLeaves T F k x)
      (frontierLeaves_level T F k x _ (Classical.choose_spec hx))
      (frontierLeaves_cone T F k x) (by omega))
  else c ((SynchronizedFrame.identity : SynchronizedFrame T).realizedCore (h + 1))

theorem frontierColor_aligned {h : ℕ} {K : Type} (c : RealizedTreeCore T (h + 1) → K)
    (hh : 0 < h) (x : VectorNode (frontierTrees T F k)) (m : ℕ)
    (hx : ∀ j, (frontierTrees T F k j).nodeHeight (x j) = m) (P : EndedCore T F k h) :
    frontierColor T F k c hh x P =
      c (appendEndedCore T F k P hh (k + 1 + m) (frontierLeaves T F k x)
        (frontierLeaves_level T F k x m hx) (frontierLeaves_cone T F k x) (by omega)) := by
  classical
  rw [frontierColor, dif_pos (show ∃ m, ∀ j, (frontierTrees T F k j).nodeHeight (x j) = m from ⟨m, hx⟩)]
  apply congrArg c
  apply appendEndedCore_eq
  · exact appendEndedCore_prefix T F k P hh _ _ _ _ _
  · intro i
    exact (appendEndedCore_last T F k P hh _ _ _ _ _ i).symm

theorem packed_height_hl [Fintype I] {h : ℕ} {K : Type} [Fintype K]
    (c : RealizedTreeCore T (h + 1) → K) (hh : 0 < h) :
    Nonempty (HomogeneousStrongVector (frontierTrees T F k) (frontierColor T F k c hh)) := by
  classical
  haveI := endedCore_finite T hh F k
  letI := Fintype.ofFinite (EndedCore T F k h)
  exact strong_subtree_ramsey_fintype (frontierTrees T F k) (EndedCore T F k h → K)
    (frontierColor T F k c hh)

def homogeneousFrontierForest {K : Type} {d : VectorNode (frontierTrees T F k) → K}
    (H : HomogeneousStrongVector (frontierTrees T F k) d) : FrontierForest T F k where
  index := H.index
  index_strictMono := H.index_strictMono
  frames i a := H.frames ⟨i, a⟩
  frame_index i a := H.frame_index ⟨i, a⟩

theorem homogeneous_frontier_extension {h : ℕ} {K : Type}
    (c : RealizedTreeCore T (h + 1) → K) (hh : 0 < h)
    (H : HomogeneousStrongVector (frontierTrees T F k) (frontierColor T F k c hh))
    (P : EndedCore T F k h) (r : ℕ)
    (x : ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i)
    (hx : ∀ i a, x i a ∈ ((homogeneousFrontierForest T F k H).frames i a).nodes r) :
    c (appendEndedCore T F k P hh (k + 1 + H.index r) x
      (fun i a => forest_nodes_level T F k (homogeneousFrontierForest T F k H) i a r (hx i a))
      (fun i a => forest_nodes_cone T F k (homogeneousFrontierForest T F k H) i a r (hx i a))
      (by omega)) = H.color P := by
  let y : VectorNode (frontierTrees T F k) := fun j =>
    ⟨x j.1 j.2, H.index r, by
      have h := (H.frames j).nodes_subset r (hx j.1 j.2)
      rwa [H.frame_index] at h⟩
  have hy : ∀ j, (frontierTrees T F k j).nodeHeight (y j) = H.index r := by
    intro j
    apply (frontierTrees T F k j).nodeHeight_eq
    have h := (H.frames j).nodes_subset r (hx j.1 j.2)
    rwa [H.frame_index] at h
  have hc := congrFun (H.colored r y (fun j => hx j.1 j.2)) P
  rw [frontierColor_aligned T F k c hh y (H.index r) hy P] at hc
  exact hc

end RelationalRamsey632.Milliken
