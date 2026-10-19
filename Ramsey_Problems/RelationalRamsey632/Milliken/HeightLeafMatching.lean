import RelationalRamsey632.Milliken.HeightFrontier

/-! Required successor cones have exactly one actual final leaf. Unused
cones are filled independently, so every end core is represented by a
full Cartesian frontier tuple seen by the packed HL color. -/

namespace RelationalRamsey632.Milliken.HeightLeafMatching

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    (T : FiniteLevelTree α R) (e f : ℕ → ℕ) (h k m : ℕ)
    (P : FiniteStrongPrefix T e h) (Q : FiniteStrongPrefix T f (h + 1))
    (hh : 0 < h) (hfLast : f (h - 1) = k) (hfEnd : f h = m)
    (hprefix : ∀ n, n < h → Q.nodes n = P.nodes n)

include hh hfLast hprefix

theorem unique_required_leaf (a : ConeAnchor T (k + 1))
    (ha : a ∈ HeightFrontier.requiredAnchors T e h k P) :
    ∃! w, w ∈ Q.nodes h ∧ R a.val w := by
  obtain ⟨u, hu, hua⟩ := (HeightFrontier.mem_requiredAnchors T e h k P a).mp ha
  have hlast : h - 1 < h := Nat.sub_lt hh (by decide)
  have hsucc : h - 1 + 1 = h := Nat.sub_add_cancel (Nat.succ_le_of_lt hh)
  have huQ : u ∈ Q.nodes (h - 1) := by rw [hprefix _ hlast]; exact hu
  have haQ : a.val ∈ T.nodes (f (h - 1) + 1) := by rw [hfLast]; exact a.property
  have he := Q.successor (h - 1) (by omega) u huQ a.val haQ hua
  simpa only [hsucc] using he

omit hh hfLast hprefix

variable (H : ∀ a : ConeAnchor T (k + 1), (coneTree T (k + 1) a).StrongFrame) (r : ℕ)
    (hcover : Q.nodes h ⊆ Finset.univ.biUnion (fun a => (H a).nodes r))

include hfEnd hcover

theorem leaf_in_own_cone (a : ConeAnchor T (k + 1)) (w : α)
    (hw : w ∈ Q.nodes h) (haw : R a.val w) : w ∈ (H a).nodes r := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp (hcover hw)
  have hbT := (H b).nodes_subset r hb
  have hbw := coneTree_below T (k + 1) b ((H b).index r) w hbT
  have hwT : w ∈ T.nodes m := by
    have hv := Q.nodes_subset h (Nat.lt_succ_self h) hw
    rwa [hfEnd] at hv
  have hab : a = b := Subtype.ext
    (T.node_eq_of_common_extension (k + 1) m a.val b.val w
      a.property b.property hwT haw hbw)
  exact hab.symm ▸ hb

omit hfEnd hcover

theorem match_leaves (hh : 0 < h) (hfLast : f (h - 1) = k) (hfEnd : f h = m)
    (hprefix : ∀ n, n < h → Q.nodes n = P.nodes n) (hkm : k < m)
    (hcover : Q.nodes h ⊆ Finset.univ.biUnion (fun a => (H a).nodes r)) :
    ∃ x : ConeAnchor T (k + 1) → α,
      (∀ a, x a ∈ (H a).nodes r) ∧
      HeightFrontier.lastNodes T e h k P x = Q.nodes h := by
  classical
  have hreq : ∀ a, a ∈ HeightFrontier.requiredAnchors T e h k P →
      ∃ w, w ∈ (H a).nodes r ∧ w ∈ Q.nodes h ∧ R a.val w := by
    intro a ha
    obtain ⟨w, hw, _⟩ := unique_required_leaf T e f h k P Q hh hfLast hprefix a ha
    exact ⟨w, leaf_in_own_cone T f h k m Q hfEnd H r hcover a w hw.1 hw.2, hw⟩
  let x : ConeAnchor T (k + 1) → α := fun a =>
    if ha : a ∈ HeightFrontier.requiredAnchors T e h k P then Classical.choose (hreq a ha)
    else ((H a).toTree.nodes_nonempty r).choose
  have hx : ∀ a, x a ∈ (H a).nodes r := by
    intro a
    by_cases ha : a ∈ HeightFrontier.requiredAnchors T e h k P
    · simp only [x, dif_pos ha]
      exact (Classical.choose_spec (hreq a ha)).1
    · simp only [x, dif_neg ha]
      exact ((H a).toTree.nodes_nonempty r).choose_spec
  have hxQ : ∀ a, a ∈ HeightFrontier.requiredAnchors T e h k P →
      x a ∈ Q.nodes h ∧ R a.val (x a) := by
    intro a ha
    simp only [x, dif_pos ha]
    exact (Classical.choose_spec (hreq a ha)).2
  refine ⟨x, hx, ?_⟩
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    exact (hxQ a ha).1
  · intro w hw
    have hsucc : h - 1 + 1 = h := Nat.sub_add_cancel (Nat.succ_le_of_lt hh)
    have hw' : w ∈ Q.nodes (h - 1 + 1) := hsucc.symm ▸ hw
    obtain ⟨u, hu, huw⟩ := Q.parent (h - 1) (by omega) w hw'
    have huP : u ∈ P.nodes (h - 1) := by
      rwa [hprefix _ (Nat.sub_lt hh (by decide))] at hu
    have huT : u ∈ T.nodes k := by
      have hv := Q.nodes_subset (h - 1) (by omega) hu
      rwa [hfLast] at hv
    have hwT : w ∈ T.nodes m := by
      have hv := Q.nodes_subset h (Nat.lt_succ_self h) hw
      rwa [hfEnd] at hv
    obtain ⟨v, ⟨hv, hvw⟩, _⟩ :=
      T.ancestor (k + 1) m (Nat.succ_le_of_lt hkm) w hwT
    have huv : R u v := T.ancestor_comparable k (k + 1) m
      (Nat.le_succ k) u v w huT hv hwT huw hvw
    let a : ConeAnchor T (k + 1) := ⟨v, hv⟩
    have ha : a ∈ HeightFrontier.requiredAnchors T e h k P :=
      (HeightFrontier.mem_requiredAnchors T e h k P a).mpr ⟨u, huP, huv⟩
    obtain ⟨z, _, huniq⟩ := unique_required_leaf T e f h k P Q hh hfLast hprefix a ha
    have hwa : w = x a := (huniq w ⟨hw, hvw⟩).trans (huniq (x a) (hxQ a ha)).symm
    exact Finset.mem_image.mpr ⟨a, ha, hwa.symm⟩

section Vector

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    (e f : ℕ → ℕ) (h k m : ℕ)
    (P : ∀ i, FiniteStrongPrefix (T i) e h)
    (Q : ∀ i, FiniteStrongPrefix (T i) f (h + 1))
    (H : ∀ i, ∀ a : ConeAnchor (T i) (k + 1), (coneTree (T i) (k + 1) a).StrongFrame)
    (r : ℕ)

theorem match_vector_leaves (hh : 0 < h) (hfLast : f (h - 1) = k) (hfEnd : f h = m)
    (hprefix : ∀ i n, n < h → (Q i).nodes n = (P i).nodes n) (hkm : k < m)
    (hcover : ∀ i, (Q i).nodes h ⊆ Finset.univ.biUnion (fun a => (H i a).nodes r)) :
    ∃ x : ∀ i, ConeAnchor (T i) (k + 1) → α i,
      (∀ i a, x i a ∈ (H i a).nodes r) ∧
      ∀ i, HeightFrontier.lastNodes (T i) e h k (P i) (x i) = (Q i).nodes h := by
  classical
  have hi := fun i => match_leaves (T i) e f h k m (P i) (Q i) (H i) r
    hh hfLast hfEnd (hprefix i) hkm (hcover i)
  refine ⟨fun i => Classical.choose (hi i), ?_, ?_⟩
  · exact fun i => (Classical.choose_spec (hi i)).1
  · exact fun i => (Classical.choose_spec (hi i)).2

end Vector

end RelationalRamsey632.Milliken.HeightLeafMatching
