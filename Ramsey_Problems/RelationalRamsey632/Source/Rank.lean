import RelationalRamsey632.Source.Closure
import Mathlib.Data.Finset.Card

/-! The strengthened triangular domain bound after compression. -/

namespace RelationalRamsey632.Source

def levelRank (L : Finset ℕ) (n : ℕ) : ℕ :=
  (L.filter (fun m => m < n)).card

theorem levelRank_mono (L : Finset ℕ) {m n : ℕ} (h : m ≤ n) :
    levelRank L m ≤ levelRank L n := by
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hx, hm⟩
  exact Finset.mem_filter.mpr ⟨hx, hm.trans_le h⟩

theorem levelRank_strict (L : Finset ℕ) {m n : ℕ}
    (hm : m ∈ L) (h : m < n) : levelRank L m < levelRank L n := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, hxm⟩
    exact Finset.mem_filter.mpr ⟨hx, hxm.trans h⟩
  · intro he
    have hm' : m ∈ L.filter (fun x => x < n) :=
      Finset.mem_filter.mpr ⟨hm, h⟩
    rw [← he] at hm'
    exact (Nat.lt_irrefl m) (Finset.mem_filter.mp hm').2

theorem levelRank_lt_card (L : Finset ℕ) {n : ℕ} (hn : n ∈ L) :
    levelRank L n < L.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have hn' : n ∈ L.filter (fun x => x < n) := he.symm ▸ hn
  exact (Nat.lt_irrefl n) (Finset.mem_filter.mp hn').2

theorem generated_rank_bound {A : ℕ → Type} {X : Set (Node A 0)}
    (L : Finset ℕ) (hL : closureLevels A X ⊆ (L : Set ℕ)) :
    ∀ x, Generated A X x →
    (match x with
    | .inl ⟨i, t⟩ => i + levelRank L t.height < L.card
    | .inr n => levelRank L n < L.card) := by
  intro x hx
  induction hx with
  | generator t ht =>
    simpa using levelRank_lt_card L (hL (Generated.height t (Generated.generator t ht)))
  | height t ht ih =>
    dsimp only at ih ⊢
    omega
  | meet s t hs ht ihs iht =>
    dsimp only at ihs iht ⊢
    have h := levelRank_mono L (Node.meetHeight_le_left s t)
    change _ + levelRank L (Node.meetHeight s t) < L.card
    omega
  | restrict t n ht hn h iht ihn =>
    dsimp only at iht ihn ⊢
    have hr := levelRank_mono L h
    change _ + levelRank L n < L.card
    omega
  | slice t n ht hn h iht ihn =>
    dsimp only at iht ihn ⊢
    have hr := levelRank_strict L (hL hn) h
    change _ + 1 + levelRank L n < L.card
    omega

/-- Every retained node is inside the finite-vector triangular valuation domain. -/
theorem closure_node_rank_bound {A : ℕ → Type} {X : Set (Node A 0)}
    (L : Finset ℕ) (hL : closureLevels A X ⊆ (L : Set ℕ))
    {i : ℕ} {t : Node A i} (ht : t ∈ closureNodes A X i) :
    i + levelRank L t.height < L.card :=
  generated_rank_bound L hL _ ht

theorem closure_rank_high_sort_empty {A : ℕ → Type} {X : Set (Node A 0)}
    (L : Finset ℕ) (hL : closureLevels A X ⊆ (L : Set ℕ))
    {i : ℕ} (hi : L.card ≤ i) : closureNodes A X i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := closure_node_rank_bound L hL ht
  omega

end RelationalRamsey632.Source
