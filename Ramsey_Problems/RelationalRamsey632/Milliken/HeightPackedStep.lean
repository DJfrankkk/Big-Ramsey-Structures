import RelationalRamsey632.Milliken.HeightPackedColor
import RelationalRamsey632.Milliken.HeightCandidateStage
import RelationalRamsey632.Milliken.HeightLeafMatching

/-!
The actual one-stage canonization.  Every end extension, rather than only a
chosen subfamily, is represented by the homogeneous full-frontier tuple.
-/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

theorem canonical_step_nonempty [Fintype I] [Nonempty I] {h : ℕ} {K : Type} [Fintype K]
    (c : RealizedTreeCore T (h + 1) → K) (hh : 0 < h) : CanonicalStep T c := by
  classical
  intro F k
  obtain ⟨H⟩ := packed_height_hl T F k c hh
  let B := homogeneousFrontierForest T F k H
  let G := forestRefinement T F k B
  refine ⟨G, forestRefinement_preserves T F k B, ?_⟩
  intro P hP
  let p : EndedCore T F k h := ⟨P, hP⟩
  refine ⟨H.color p, ?_⟩
  intro C hC hprefix
  obtain ⟨r, f, _hf, Q, hfLast, hfEnd, hQprefix, hQlast, hQcover⟩ :=
    HeightCandidateStage.candidate_native_prefix T F k hh p B C hC hprefix
  obtain ⟨x, hx, hxlast⟩ := HeightLeafMatching.match_vector_leaves
    (fun i => (F.frames i).toTree) (endedSelector T F k p) f h k (k + 1 + B.index r)
    (endedPrefix T F k p) Q B.frames r hh hfLast hfEnd hQprefix (by omega) hQcover
  have he : appendEndedCore T F k p hh (k + 1 + H.index r) x
      (fun i a => forest_nodes_level T F k B i a r (hx i a))
      (fun i a => forest_nodes_cone T F k B i a r (hx i a)) (by omega) = C := by
    apply appendEndedCore_eq
    · exact hprefix
    · intro i
      exact (hxlast i).trans (hQlast i)
  have hc := homogeneous_frontier_extension T F k c hh H p r x hx
  rw [he] at hc
  exact hc

theorem core_eq_empty_index [IsEmpty I] {h : ℕ} (C D : RealizedTreeCore T h) : C = D := by
  apply Subtype.ext
  funext i
  exact isEmptyElim i

theorem canonical_step_empty [IsEmpty I] {h : ℕ} {K : Type}
    (c : RealizedTreeCore T (h + 1) → K) : CanonicalStep T c := by
  intro F k
  refine ⟨FrameRefinement.identity F, FrameRefinement.identity_preserves F k, ?_⟩
  intro P _
  refine ⟨c (F.realizedCore (h + 1)), ?_⟩
  intro C _ _
  exact congrArg c (core_eq_empty_index T C (F.realizedCore (h + 1)))

theorem canonical_step [Fintype I] {h : ℕ} {K : Type} [Fintype K]
    (c : RealizedTreeCore T (h + 1) → K) (hh : 0 < h) : CanonicalStep T c := by
  classical
  by_cases hI : Nonempty I
  · letI := hI
    exact canonical_step_nonempty T c hh
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    exact canonical_step_empty T c

end RelationalRamsey632.Milliken
