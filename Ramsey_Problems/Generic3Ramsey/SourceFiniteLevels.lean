import Generic3Ramsey.SourcePrefixSystem

/-! Explicit finite enumeration of every level of an actual prefix system. -/

namespace Generic3Ramsey.SourceTrees.StrongPrefixSystem

variable {α : Type} [DecidableEq α] (S : StrongPrefixSystem α)

noncomputable def canonicalNext (n : ℕ) (u : List α) (a : α) : List α := by
  classical
  exact if h : u ∈ S.nodes n ∧ a ∈ S.children n then
    Classical.choose (S.successor n u h.1 a h.2) else []

theorem canonicalNext_spec (n : ℕ) (u : List α) (hu : u ∈ S.nodes n)
    (a : α) (ha : a ∈ S.children n) :
    S.canonicalNext n u a ∈ S.nodes (n + 1) ∧ u ++ [a] <+: S.canonicalNext n u a := by
  have hg : u ∈ S.nodes n ∧ a ∈ S.children n := ⟨hu, ha⟩
  simp only [canonicalNext, dif_pos hg]
  exact (Classical.choose_spec (S.successor n u hu a ha)).1

theorem canonicalNext_eq (n : ℕ) (u : List α) (hu : u ∈ S.nodes n)
    (a : α) (ha : a ∈ S.children n) (v : List α)
    (hv : v ∈ S.nodes (n + 1)) (hcone : u ++ [a] <+: v) :
    S.canonicalNext n u a = v := by
  have hg : u ∈ S.nodes n ∧ a ∈ S.children n := ⟨hu, ha⟩
  simp only [canonicalNext, dif_pos hg]
  exact ((Classical.choose_spec (S.successor n u hu a ha)).2 v ⟨hv, hcone⟩).symm

noncomputable def finiteNodes (data : StrongPrefixSystem α) : ℕ → Finset (List α)
  | 0 => {data.root}
  | n + 1 => (finiteNodes data n).biUnion fun u => (data.children n).image (data.canonicalNext n u)

theorem mem_finiteNodes (n : ℕ) (u : List α) : u ∈ S.finiteNodes n ↔ u ∈ S.nodes n := by
  induction n generalizing u with
  | zero =>
      constructor
      · intro hu
        have he : u = S.root := Finset.mem_singleton.mp hu
        exact he ▸ S.root_mem
      · intro hu
        exact Finset.mem_singleton.mpr (S.root_unique u hu)
  | succ n ih =>
      constructor
      · intro hu
        obtain ⟨v, hv, hua⟩ := Finset.mem_biUnion.mp hu
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hua
        exact (S.canonicalNext_spec n v ((ih v).mp hv) a ha).1
      · intro hu
        obtain ⟨v, hv, a, ha, hcone⟩ := S.parent n u hu
        apply Finset.mem_biUnion.mpr
        exact ⟨v, (ih v).mpr hv, Finset.mem_image.mpr
          ⟨a, ha, S.canonicalNext_eq n v hv a ha u hu hcone⟩⟩

theorem finiteNodes_nonempty (n : ℕ) : (S.finiteNodes n).Nonempty := by
  obtain ⟨v, hv, _⟩ := S.extend 0 n (Nat.zero_le n) S.root S.root_mem
  exact ⟨v, (S.mem_finiteNodes n v).mpr hv⟩

theorem nodes_finite (n : ℕ) : (S.nodes n).Finite := by
  have he : (↑(S.finiteNodes n) : Set (List α)) = S.nodes n := by
    ext u
    exact S.mem_finiteNodes n u
  rw [← he]
  exact (S.finiteNodes n).finite_toSet

end Generic3Ramsey.SourceTrees.StrongPrefixSystem
