import RelationalRamsey632.Milliken.HeightFrames
import RelationalRamsey632.Milliken.SectionFusionBridge

/-! Transport all finite-dimensional HL instances to arbitrary finite index sets. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

theorem halpernLauchli_for_fintype (hAll : ∀ d, HalpernLauchliDimension d)
    {I : Type} [Fintype I] {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    (K : Type) [Fintype K] : StrongSubtreeRamsey T K := by
  classical
  intro c
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let T' := fun j : Fin (Fintype.card I) => T (e.symm j)
  let E : VectorNode T ≃ VectorNode T' :=
    (Equiv.piCongrLeft (fun i => (T i).TreeNode) e.symm).symm
  let EF : ((i : I) → (T i).StrongFrame) ≃ ((j : Fin (Fintype.card I)) → (T' j).StrongFrame) :=
    (Equiv.piCongrLeft (fun i => (T i).StrongFrame) e.symm).symm
  obtain ⟨H⟩ := hAll (Fintype.card I) (fun j => α (e.symm j))
    (fun j => R (e.symm j)) T' K (fun x => c (E.symm x))
  let frames : (i : I) → (T i).StrongFrame := EF.symm H.frames
  have hframe : ∀ j, frames (e.symm j) = H.frames j := by
    intro j
    exact congrFun (EF.apply_symm_apply H.frames) j
  refine ⟨⟨H.index, H.index_strictMono, frames, ?_, H.color, ?_⟩⟩
  · intro i
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    rw [hframe]
    exact H.frame_index j
  · intro n x hx
    have hx' : ∀ j, (E x j).val ∈ (H.frames j).nodes n := by
      intro j
      have h := hx (e.symm j)
      rw [hframe] at h
      exact h
    have h := H.colored n (E x) hx'
    simpa only [E.symm_apply_apply] using h

theorem strong_subtree_ramsey_fintype
    {I : Type} [Fintype I] {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    (K : Type) [Fintype K] : StrongSubtreeRamsey T K :=
  halpernLauchli_for_fintype halpernLauchli_all T K

end RelationalRamsey632.Milliken
