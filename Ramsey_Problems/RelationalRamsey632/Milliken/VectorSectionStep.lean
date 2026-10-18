import RelationalRamsey632.Milliken.PrefixForestGraft

/-! One prefix-preserving simultaneous section-stabilization step. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop}
    (T : ∀ i, FiniteLevelTree (α i) (R i))

structure JointFrame where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  frames : ∀ i, (T i).StrongFrame
  frame_index : ∀ i, (frames i).index = index

namespace JointFrame

variable {T}

def identity : JointFrame T where
  index := id
  index_strictMono := strictMono_id
  frames i := StrongFrame.identity (T i)
  frame_index _ := rfl

variable (F : JointFrame T) {β : Type} [DecidableEq β] {Q : β → β → Prop}
    (B : FiniteLevelTree β Q) {K : Type}
    (c : (∀ i, α i) → β → K) (k : ℕ)

structure SectionStep where
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  subframes : ∀ i, (F.frames i).toTree.StrongFrame
  common_index : ∀ i, (subframes i).index = selector
  preserved : ∀ i n, n ≤ k →
    selector n = n ∧ (subframes i).nodes n = (F.frames i).nodes n
  stable : ∀ z ∈ B.nodes k, ∀ n m, k < n → n ≤ m → ∀ x y : ∀ i, α i,
    (∀ i, x i ∈ (subframes i).nodes n) →
    (∀ i, y i ∈ (subframes i).nodes m) →
    (∀ i, R i (x i) (y i)) → c x z = c y z

noncomputable def SectionStep.next (S : F.SectionStep B c k) : JointFrame T where
  index := F.index ∘ S.selector
  index_strictMono := F.index_strictMono.comp S.selector_strictMono
  frames i := (F.frames i).comp (S.subframes i)
  frame_index i := by
    funext n
    change (F.frames i).index ((S.subframes i).index n) = F.index (S.selector n)
    rw [F.frame_index, S.common_index]

def UniformSameDimensionSS : Prop :=
  ∀ (D : Type) [Fintype D], SameDimensionSS (α := α) (R := R) D

omit [DecidableEq I] in
theorem sectionStep_exists [Fintype K]
    (hSS : UniformSameDimensionSS (α := α) (R := R)) :
    Nonempty (F.SectionStep B c k) := by
  classical
  let A := fun i => ConeAnchor (F.frames i).toTree (k + 1)
  let C := fun i (a : A i) => coneTree (F.frames i).toTree (k + 1) a
  let F0 : StrongForest C := {
    index := id
    index_strictMono := strictMono_id
    frames i a := StrongFrame.identity (C i a)
    frame_index _ _ := rfl
  }
  let Z := {z : β // z ∈ B.nodes k}
  let palette := fun x : ∀ i, α i => fun z : Z => c x z.val
  obtain ⟨G, hG⟩ := all_frontier_stabilization C (hSS (Z → K)) F0 palette
  let F1 := G.forest
  let H := fun i => PrefixForestGraft.frame (F.frames i).toTree k F1.index
    F1.index_strictMono (F1.frames i) (F1.frame_index i)
  let select := PrefixForestGraft.index k F1.index
  refine ⟨{
    selector := select
    selector_strictMono := PrefixForestGraft.index_strictMono k F1.index F1.index_strictMono
    subframes := H
    common_index := fun _ => rfl
    preserved := ?_
    stable := ?_
  }⟩
  · intro i n hn
    exact PrefixForestGraft.frame_preserved (F.frames i).toTree k F1.index
      F1.index_strictMono (F1.frames i) (F1.frame_index i) n hn
  · intro z hz n m hkn hnm x y hx hy hxy
    let r := n - k - 1
    let s := m - k - 1
    have hn : n = k + 1 + r := by dsimp [r]; omega
    have hm : m = k + 1 + s := by dsimp [s]; omega
    have hAx : ∀ i, ∃ a : A i, x i ∈ (F1.frames i a).nodes r := by
      intro i
      have hi := hx i
      change x i ∈ PrefixForestGraft.nodes (F.frames i).toTree k (F1.frames i) n at hi
      rw [hn, PrefixForestGraft.nodes_tail] at hi
      exact (PrefixForestGraft.mem_tailNodes (F.frames i).toTree k (F1.frames i) r (x i)).mp hi
    let p : ∀ i, A i := fun i => Classical.choose (hAx i)
    have hpx : ∀ i, x i ∈ (F1.frames i (p i)).nodes r :=
      fun i => Classical.choose_spec (hAx i)
    have hpy : ∀ i, y i ∈ (F1.frames i (p i)).nodes s := by
      intro i
      have hi := hy i
      change y i ∈ PrefixForestGraft.nodes (F.frames i).toTree k (F1.frames i) m at hi
      rw [hm, PrefixForestGraft.nodes_tail] at hi
      obtain ⟨a, ha⟩ := (PrefixForestGraft.mem_tailNodes (F.frames i).toTree k
        (F1.frames i) s (y i)).mp hi
      have hpa := PrefixForestGraft.anchor_eq_of_descendants (F.frames i).toTree k
        (F1.frames i) r s (p i) a (x i) (y i) (hpx i) ha (hxy i)
      exact hpa.symm ▸ ha
    obtain ⟨color, hc⟩ := hG p
    have hcx := congrFun (hc r x hpx) (⟨z, hz⟩ : Z)
    have hcy := congrFun (hc s y hpy) (⟨z, hz⟩ : Z)
    exact hcx.trans hcy.symm

end JointFrame

end RelationalRamsey632.Milliken
