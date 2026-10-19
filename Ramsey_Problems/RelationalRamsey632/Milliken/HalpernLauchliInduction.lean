import RelationalRamsey632.Milliken.FinDimension

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

/-- This is a statement about actual constructed stabilizing frames. Its
lower-dimensional SS premise is the induction hypothesis; no Ramsey
statement of dimension d+1 is present. -/
def SectionFusionPrinciple (d : ℕ) : Prop :=
  ∀ (α : Fin d → Type) [∀ i, DecidableEq (α i)]
    (R : ∀ i, α i → α i → Prop) (T : ∀ i, FiniteLevelTree (α i) (R i))
    (β : Type) [DecidableEq β] (Q : β → β → Prop) (B : FiniteLevelTree β Q)
    (K : Type) [Fintype K] (c : VectorNode T → B.TreeNode → K),
    (∀ (C : Type) [Fintype C],
      ∀ S : ∀ i, FiniteLevelTree (α i) (R i), StrongSubtreeRamsey S C) →
      ∃ e : ℕ → ℕ, ∃ frames : ∀ i, (T i).StrongFrame,
        (∀ i, (frames i).index = e) ∧
          StableVectorSections (fun i => (frames i).toTree) B
            (fun x y => c (fun i => (frames i).nodeMap632 (x i)) y)

theorem mixed_successor_of_section_fusion {d : ℕ} (hd : 0 < d)
    (hLower : HalpernLauchliDimension d) (hSections : SectionFusionPrinciple d)
    {α : Fin (d + 1) → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    (K : Type) [Fintype K] : MixedSDHL T K := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro c
  let first := fun i : Fin d => T i.castSucc
  let last := T (Fin.last d)
  let c' := fun (x : VectorNode first) (y : last.TreeNode) => c (Fin.lastCases y x)
  have hSame : ∀ (C : Type) [Fintype C],
      ∀ S : ∀ i : Fin d, FiniteLevelTree (α i.castSucc) (R i.castSucc),
        StrongSubtreeRamsey S C := by
    intro C _ S
    exact hLower (fun i : Fin d => α i.castSucc) (fun i => R i.castSucc) S C
  obtain ⟨e, frames, hindex, hstable⟩ := hSections
    (fun i : Fin d => α i.castSucc) (fun i => R i.castSucc) first
    (α (Fin.last d)) (R (Fin.last d)) last K c' hSame
  have hmatrix := dimension_matrix_of_stable_frames first last (hSame K) c' e frames hindex hstable
  exact mixed_last_to_full T c hmatrix

/-- The complete logical dimension step: lower-dimensional strong HL,
constructed section fusion, branch-density selection, mixed SDHL,
compactness synchronization, density strengthening, and strong-frame fusion. -/
theorem halpernLauchli_successor {d : ℕ} (hd : 0 < d)
    (hLower : HalpernLauchliDimension d) (hSections : SectionFusionPrinciple d) :
    HalpernLauchliDimension (d + 1) := by
  classical
  intro α _ R T K _ c
  obtain ⟨depth, roots, hroot, hD⟩ := dense_sets_from_restricted_mixed T
    (fun index hm hz => mixed_successor_of_section_fusion hd hLower hSections
      (fun i => (T i).restrictLevels index hm hz) K) c
  exact strong_vector_from_dense_sets T roots c depth hroot hD

theorem halpernLauchli_all_of_section_fusion
    (hSections : ∀ d, 0 < d → SectionFusionPrinciple d) :
    ∀ d, HalpernLauchliDimension d := by
  intro d
  induction d with
  | zero => exact halpernLauchli_zero
  | succ d ih =>
    cases d with
    | zero => exact halpernLauchli_one
    | succ d =>
      exact halpernLauchli_successor (Nat.zero_lt_succ d) ih (hSections _ (Nat.zero_lt_succ d))

end RelationalRamsey632.Milliken
