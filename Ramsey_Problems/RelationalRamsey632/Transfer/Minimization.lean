import RelationalRamsey632.Transfer.CoarseRecurrence

namespace RelationalRamsey632.Transfer

open RelStructure
open scoped BigOperators

variable {L S : Language} {X : Type}

noncomputable def paletteRank {J : Type} [Fintype J] {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) : ℕ := ∑ j, (palette (a j) K Y).ncard

/-- The attained palette rank has a minimum even though the collection
of self-embeddings is not finite. -/
theorem minimum_palette_rank {J : Type} [Fintype J] {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) :
    ∃ η : RelEmbedding K K, ∀ α : RelEmbedding K K,
      paletteRank a K (Y.pullback η) ≤ paletteRank a K (Y.pullback α) := by
  classical
  let P : ℕ → Prop := fun n => ∃ η : RelEmbedding K K,
    paletteRank a K (Y.pullback η) = n
  have hex : ∃ n, P n := ⟨_, RelEmbedding.refl K, rfl⟩
  obtain ⟨η, hη⟩ := Nat.find_spec hex
  exact ⟨η, fun α => hη.trans_le (Nat.find_min' hex ⟨α, rfl⟩)⟩

/-- Any attained rank minimizer leaves every selected palette unavoidable. -/
theorem minimizing_palettes_unavoidable {J : Type} [Fintype J] {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X)
    (hfin : ∀ j, (palette (a j) K Y).Finite)
    (η : RelEmbedding K K)
    (hmin : ∀ α : RelEmbedding K K,
      paletteRank a K (Y.pullback η) ≤ paletteRank a K (Y.pullback α)) :
    ∀ j, Unavoidable (a j) K (Y.pullback η) := by
  classical
  intro j α
  have hlarge : ∀ k, (palette (a k) K (Y.pullback η)).Finite :=
    fun k => (hfin k).subset (palette_pullback_subset (a k) K Y η)
  have hsub : ∀ k,
      palette (a k) K ((Y.pullback η).pullback α) ⊆ palette (a k) K (Y.pullback η) :=
    fun k => palette_pullback_subset (a k) K (Y.pullback η) α
  have hle : ∀ k ∈ Finset.univ,
      (palette (a k) K ((Y.pullback η).pullback α)).ncard ≤
        (palette (a k) K (Y.pullback η)).ncard :=
    fun k _ => Set.ncard_le_ncard (hsub k) (hlarge k)
  have heq : (∑ k, (palette (a k) K ((Y.pullback η).pullback α)).ncard)
      = ∑ k, (palette (a k) K (Y.pullback η)).ncard := by
    apply Nat.le_antisymm (Finset.sum_le_sum hle)
    exact hmin (η.comp α)
  have hcard := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  exact Set.eq_of_subset_of_ncard_le (hsub j) (hcard j (Finset.mem_univ j)).ge
    (hlarge j)

/-- Refining a rank minimizer by a reduct self-embedding retains minimality. -/
theorem refined_minimizer {J : Type} [Fintype J] {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X)
    (hfin : ∀ j, (palette (a j) K Y).Finite)
    (η : RelEmbedding K K)
    (hmin : ∀ α : RelEmbedding K K,
      paletteRank a K (Y.pullback η) ≤ paletteRank a K (Y.pullback α))
    (β : RelEmbedding K K) :
    ∀ α : RelEmbedding K K,
      paletteRank a K (Y.pullback (η.comp β)) ≤ paletteRank a K (Y.pullback α) := by
  have hu := minimizing_palettes_unavoidable a K Y hfin η hmin
  have hr : paletteRank a K (Y.pullback (η.comp β)) = paletteRank a K (Y.pullback η) := by
    unfold paletteRank
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg Set.ncard (hu j β)
  intro α
  rw [hr]
  exact hmin α

end RelationalRamsey632.Transfer
