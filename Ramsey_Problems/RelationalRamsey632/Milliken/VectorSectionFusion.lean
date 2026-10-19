import RelationalRamsey632.Milliken.VectorSectionStep

/-! Countable section fusion from same-dimensional SS, keeping the last
tree on its original levels throughout. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

namespace VectorSectionFusion

variable {I : Type} [Fintype I] [Nonempty I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop}
    (T : ∀ i, FiniteLevelTree (α i) (R i))
    {β : Type} [DecidableEq β] {Q : β → β → Prop}
    (B : FiniteLevelTree β Q) {K : Type} [Fintype K]
    (c : (∀ i, α i) → β → K)
    (hSS : JointFrame.UniformSameDimensionSS (α := α) (R := R))

noncomputable def step (F : JointFrame T) (k : ℕ) : F.SectionStep B c k :=
  Classical.choice (F.sectionStep_exists B c k hSS)

noncomputable def stages : ℕ → JointFrame T
  | 0 => JointFrame.identity
  | k + 1 => (step T B c hSS (stages k) k).next

theorem stages_index_step (k n : ℕ) (hn : n ≤ k) :
    (stages T B c hSS (k + 1)).index n = (stages T B c hSS k).index n := by
  let i : I := Classical.choice inferInstance
  change (stages T B c hSS k).index ((step T B c hSS (stages T B c hSS k) k).selector n) = _
  rw [((step T B c hSS (stages T B c hSS k) k).preserved i n hn).1]

omit [Nonempty I] in
theorem stages_nodes_step (k n : ℕ) (hn : n ≤ k) (i : I) :
    ((stages T B c hSS (k + 1)).frames i).nodes n =
      ((stages T B c hSS k).frames i).nodes n :=
  ((step T B c hSS (stages T B c hSS k) k).preserved i n hn).2

theorem stages_index_fixed (n r s : ℕ) (hnr : n ≤ r) (hrs : r ≤ s) :
    (stages T B c hSS s).index n = (stages T B c hSS r).index n := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    exact (stages_index_step T B c hSS s n (hnr.trans hrs)).trans ih

omit [Nonempty I] in
theorem stages_nodes_fixed (n r s : ℕ) (hnr : n ≤ r) (hrs : r ≤ s) (i : I) :
    ((stages T B c hSS s).frames i).nodes n =
      ((stages T B c hSS r).frames i).nodes n := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
    exact (stages_nodes_step T B c hSS s n (hnr.trans hrs) i).trans ih

omit [Nonempty I] in
theorem node_in_earlier (r s : ℕ) (hrs : r ≤ s) (i : I) :
    ∀ n u, u ∈ ((stages T B c hSS s).frames i).nodes n →
      ∃ j ≥ n, u ∈ ((stages T B c hSS r).frames i).nodes j := by
  induction s, hrs using Nat.le_induction with
  | base => exact fun n u hu => ⟨n, le_rfl, hu⟩
  | succ s hrs ih =>
    intro n u hu
    let S := step T B c hSS (stages T B c hSS s) s
    have huS : u ∈ (S.subframes i).nodes n := hu
    have huOld : u ∈ ((stages T B c hSS s).frames i).nodes (S.selector n) := by
      have h := (S.subframes i).nodes_subset n huS
      change u ∈ ((stages T B c hSS s).frames i).nodes ((S.subframes i).index n) at h
      rwa [S.common_index] at h
    obtain ⟨j, hj, huj⟩ := ih (S.selector n) u huOld
    have hindex : n ≤ S.selector n := by
      simpa only [S.common_index] using (S.subframes i).index_ge n
    exact ⟨j, hindex.trans hj, huj⟩

noncomputable def fusionIndex (n : ℕ) : ℕ := (stages T B c hSS n).index n

theorem fusionIndex_strictMono : StrictMono (fusionIndex T B c hSS) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (stages T B c hSS n).index n < (stages T B c hSS (n + 1)).index (n + 1)
  rw [← stages_index_step T B c hSS n n le_rfl]
  exact (stages T B c hSS (n + 1)).index_strictMono (Nat.lt_succ_self n)

noncomputable def fusionFrame (i : I) : (T i).StrongFrame where
  index := fusionIndex T B c hSS
  index_strictMono := fusionIndex_strictMono T B c hSS
  nodes := fun n => ((stages T B c hSS n).frames i).nodes n
  root := (T i).root
  nodes_zero := (T i).nodes_zero
  nodes_subset n := by
    have h := ((stages T B c hSS n).frames i).nodes_subset n
    rw [(stages T B c hSS n).frame_index i] at h
    exact h
  parent := by
    intro n w hw
    obtain ⟨u, hu, huw⟩ := ((stages T B c hSS (n + 1)).frames i).parent n w hw
    rw [stages_nodes_step T B c hSS n n le_rfl i] at hu
    exact ⟨u, hu, huw⟩
  successor := by
    intro n u hu v hv huv
    have hu' : u ∈ ((stages T B c hSS (n + 1)).frames i).nodes n := by
      rw [stages_nodes_step T B c hSS n n le_rfl i]
      exact hu
    have hv' : v ∈ (T i).nodes (((stages T B c hSS (n + 1)).frames i).index n + 1) := by
      rw [(stages T B c hSS (n + 1)).frame_index i,
        stages_index_step T B c hSS n n le_rfl]
      exact hv
    exact ((stages T B c hSS (n + 1)).frames i).successor n u hu' v hv' huv

theorem fusionFrame_index (i : I) : (fusionFrame T B c hSS i).index = fusionIndex T B c hSS := rfl

theorem vector_in_earlier (r n : ℕ) (hrn : r ≤ n) (x : ∀ i, α i)
    (hx : ∀ i, x i ∈ (fusionFrame T B c hSS i).nodes n) :
    ∃ j ≥ n, (stages T B c hSS r).index j = fusionIndex T B c hSS n ∧
      ∀ i, x i ∈ ((stages T B c hSS r).frames i).nodes j := by
  let i0 : I := Classical.choice inferInstance
  obtain ⟨j, hj, hxj⟩ := node_in_earlier T B c hSS r n hrn i0 n (x i0) (hx i0)
  have hjindex : (stages T B c hSS r).index j = fusionIndex T B c hSS n := by
    have hleft := ((stages T B c hSS r).frames i0).nodes_subset j hxj
    rw [(stages T B c hSS r).frame_index i0] at hleft
    exact (T i0).level_unique _ _ (x i0) hleft
      ((fusionFrame T B c hSS i0).nodes_subset n (hx i0))
  refine ⟨j, hj, hjindex, ?_⟩
  intro i
  obtain ⟨l, _, hxl⟩ := node_in_earlier T B c hSS r n hrn i n (x i) (hx i)
  have hlindex : (stages T B c hSS r).index l = fusionIndex T B c hSS n := by
    have hleft := ((stages T B c hSS r).frames i).nodes_subset l hxl
    rw [(stages T B c hSS r).frame_index i] at hleft
    exact (T i).level_unique _ _ (x i) hleft
      ((fusionFrame T B c hSS i).nodes_subset n (hx i))
  have hlj : l = j := (stages T B c hSS r).index_strictMono.injective
    (hlindex.trans hjindex.symm)
  exact hlj ▸ hxl

theorem fusion_stable (k : ℕ) (z : β) (hz : z ∈ B.nodes k)
    (n m : ℕ) (hkn : k < n) (hnm : n ≤ m) (x y : ∀ i, α i)
    (hx : ∀ i, x i ∈ (fusionFrame T B c hSS i).nodes n)
    (hy : ∀ i, y i ∈ (fusionFrame T B c hSS i).nodes m)
    (hxy : ∀ i, R i (x i) (y i)) : c x z = c y z := by
  obtain ⟨j, hj, hjindex, hxj⟩ :=
    vector_in_earlier T B c hSS (k + 1) n (by omega) x hx
  obtain ⟨l, hl, hlindex, hyl⟩ :=
    vector_in_earlier T B c hSS (k + 1) m (by omega) y hy
  have hjl : j ≤ l := by
    apply (stages T B c hSS (k + 1)).index_strictMono.le_iff_le.mp
    rw [hjindex, hlindex]
    exact (fusionIndex_strictMono T B c hSS).monotone hnm
  exact (step T B c hSS (stages T B c hSS k) k).stable
    z hz j l (hkn.trans_le hj) hjl x y hxj hyl hxy

end VectorSectionFusion

/-- Same-dimensional SS gives a common first-vector level sequence on which
every original-level section in the last tree is eventually stable. -/
theorem raw_section_fusion {I : Type} [Fintype I] [Nonempty I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop}
    (T : ∀ i, FiniteLevelTree (α i) (R i))
    {β : Type} [DecidableEq β] {Q : β → β → Prop}
    (B : FiniteLevelTree β Q) {K : Type} [Fintype K]
    (c : (∀ i, α i) → β → K)
    (hSS : JointFrame.UniformSameDimensionSS (α := α) (R := R)) :
    ∃ e : ℕ → ℕ, ∃ _he : StrictMono e, ∃ F : ∀ i, (T i).StrongFrame,
      (∀ i, (F i).index = e) ∧
      ∀ k z, z ∈ B.nodes k → ∀ n m, k < n → n ≤ m →
        ∀ x y : ∀ i, α i,
          (∀ i, x i ∈ (F i).nodes n) →
          (∀ i, y i ∈ (F i).nodes m) →
          (∀ i, R i (x i) (y i)) → c x z = c y z := by
  exact ⟨VectorSectionFusion.fusionIndex T B c hSS,
    VectorSectionFusion.fusionIndex_strictMono T B c hSS,
    VectorSectionFusion.fusionFrame T B c hSS,
    VectorSectionFusion.fusionFrame_index T B c hSS,
    VectorSectionFusion.fusion_stable T B c hSS⟩

end RelationalRamsey632.Milliken
