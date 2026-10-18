import RelationalRamsey632.Source.CompressionMeets

namespace RelationalRamsey632.Source

noncomputable def levelIndex (e : ℕ → ℕ) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, n = e k then Classical.choose h else 0

@[simp] theorem levelIndex_apply (e : ℕ → ℕ) (he : StrictMono e) (n : ℕ) :
    levelIndex e (e n) = n := by
  classical
  have h : ∃ k, e n = e k := ⟨n, rfl⟩
  simp only [levelIndex, dif_pos h]
  exact he.injective (Classical.choose_spec h).symm

theorem levelIndex_spec (e : ℕ → ℕ) {n : ℕ} (h : ∃ k, n = e k) :
    n = e (levelIndex e n) := by
  classical
  simp only [levelIndex, dif_pos h]
  exact Classical.choose_spec h

theorem compressOn_height {A : ℕ → Type} (e : ℕ → ℕ) (he : StrictMono e)
    {i : ℕ} (t : Node A i) (h : ∃ n, t.height = e n) :
    (compressOn e he t).height = levelIndex e t.height := by
  obtain ⟨n, hn⟩ := h
  cases t with
  | mk a t =>
    dsimp only [Node.height] at hn
    subst a
    rw [compressOn_mk e he, levelIndex_apply e he]

theorem levelIndex_compare (e : ℕ → ℕ) (he : StrictMono e)
    {m n : ℕ} (hm : ∃ k, m = e k) (hn : ∃ k, n = e k) :
    levelIndex e m ≤ levelIndex e n ↔ m ≤ n := by
  obtain ⟨i, rfl⟩ := hm
  obtain ⟨j, rfl⟩ := hn
  rw [levelIndex_apply e he, levelIndex_apply e he]
  exact he.le_iff_le.symm

theorem levelIndex_strict_compare (e : ℕ → ℕ) (he : StrictMono e)
    {m n : ℕ} (hm : ∃ k, m = e k) (hn : ∃ k, n = e k) :
    levelIndex e m < levelIndex e n ↔ m < n := by
  obtain ⟨i, rfl⟩ := hm
  obtain ⟨j, rfl⟩ := hn
  rw [levelIndex_apply e he, levelIndex_apply e he]
  exact he.lt_iff_lt.symm

end RelationalRamsey632.Source
