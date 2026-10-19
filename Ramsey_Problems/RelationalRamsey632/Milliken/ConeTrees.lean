import RelationalRamsey632.Milliken.VectorTailFusion

/-! Actual rooted descendant cones, with height measured from their anchors. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    (T : FiniteLevelTree α R)

abbrev ConeAnchor (b : ℕ) := {a : α // a ∈ T.nodes b}

noncomputable instance coneAnchorFintype (b : ℕ) : Fintype (ConeAnchor T b) :=
  inferInstanceAs (Fintype {a : α // a ∈ T.nodes b})

noncomputable def coneNodes (b : ℕ) (a : ConeAnchor T b) (n : ℕ) : Finset α := by
  classical
  exact (T.nodes (b + n)).filter (R a.val)

theorem mem_coneNodes (b : ℕ) (a : ConeAnchor T b) (n : ℕ) (v : α) :
    v ∈ coneNodes T b a n ↔ v ∈ T.nodes (b + n) ∧ R a.val v := by
  classical
  exact Finset.mem_filter

noncomputable def coneTree (b : ℕ) (a : ConeAnchor T b) : FiniteLevelTree α R where
  nodes := coneNodes T b a
  root := a.val
  nodes_zero := by
    classical
    ext v
    rw [mem_coneNodes, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hav⟩
      have hv' : v ∈ T.nodes b := by simpa using hv
      exact T.node_eq_of_common_extension b b v a.val v
        hv' a.property hv' (T.rel_refl v) hav
    · rintro rfl
      exact ⟨by rw [Nat.add_zero]; exact a.property, T.rel_refl a.val⟩
  rel_refl := T.rel_refl
  rel_trans := T.rel_trans
  rel_antisymm := T.rel_antisymm
  level_unique := by
    intro n m v hv hw
    have he := T.level_unique (b + n) (b + m) v
      ((mem_coneNodes T b a n v).mp hv).1 ((mem_coneNodes T b a m v).mp hw).1
    omega
  rel_level := by
    intro n m v w hv hw hvw
    have he := T.rel_level (b + n) (b + m) v w
      ((mem_coneNodes T b a n v).mp hv).1 ((mem_coneNodes T b a m w).mp hw).1 hvw
    omega
  ancestor := by
    intro n m hnm w hw
    obtain ⟨hw, haw⟩ := (mem_coneNodes T b a m w).mp hw
    obtain ⟨v, ⟨hv, hvw⟩, huniq⟩ :=
      T.ancestor (b + n) (b + m) (by omega) w hw
    have hav : R a.val v := T.ancestor_comparable b (b + n) (b + m)
      (by omega) a.val v w a.property hv hw haw hvw
    refine ⟨v, ⟨(mem_coneNodes T b a n v).mpr ⟨hv, hav⟩, hvw⟩, ?_⟩
    intro u hu
    exact huniq u ⟨((mem_coneNodes T b a n u).mp hu.1).1, hu.2⟩
  extend := by
    intro n m hnm v hv
    obtain ⟨hv, hav⟩ := (mem_coneNodes T b a n v).mp hv
    obtain ⟨w, hw, hvw⟩ := T.extend (b + n) (b + m) (by omega) v hv
    exact ⟨w, (mem_coneNodes T b a m w).mpr ⟨hw, T.rel_trans hav hvw⟩, hvw⟩

theorem coneTree_nodes_subset (b : ℕ) (a : ConeAnchor T b) (n : ℕ) :
    (coneTree T b a).nodes n ⊆ T.nodes (b + n) :=
  fun _ h => ((mem_coneNodes T b a n _).mp h).1

theorem coneTree_below (b : ℕ) (a : ConeAnchor T b) (n : ℕ) (v : α)
    (hv : v ∈ (coneTree T b a).nodes n) : R a.val v :=
  ((mem_coneNodes T b a n v).mp hv).2

end RelationalRamsey632.Milliken
