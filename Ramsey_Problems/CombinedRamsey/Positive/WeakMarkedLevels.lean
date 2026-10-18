import CombinedRamsey.Positive.WeakContainer
import CombinedRamsey.Positive.SliceLibraryCount
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum

/-! The exact R(k) estimate from an all-sort library and the weak original-level trap. -/

namespace CombinedRamsey.Positive

open RelationalRamsey632.Source

variable {A : ℕ → Type} [∀ j, Zero (A j)]

abbrev FamilyIndex (F : (i : ℕ) → Set (Node A i)) := (i : ℕ) × F i

abbrev WeakLevelIndex (F : (i : ℕ) → Set (Node A i)) (H : Finset ℕ) :=
  H ⊕ ((FamilyIndex F × FamilyIndex F) ⊕ (FamilyIndex F ⊕ FamilyIndex F))

noncomputable def weakLevelMark (F : (i : ℕ) → Set (Node A i))
    (N : ℕ) (H : Finset ℕ) : WeakLevelIndex F H → ℕ := by
  classical
  exact fun q => match q with
  | .inl n => n.val
  | .inr (.inl (s, t)) =>
      if h : s.1 = t.1 then s.2.val.meetHeight (cast (congrArg (Node A) h.symm) t.2.val)
      else N
  | .inr (.inr (.inl s)) => s.2.val.meetHeight (Node.zero s.1 N)
  | .inr (.inr (.inr t)) => (Node.zero t.1 N).meetHeight t.2.val

def weakMarkedSet (F : (i : ℕ) → Set (Node A i)) (N : ℕ) (H : Finset ℕ) : Set ℕ :=
  Set.range (weakLevelMark F N H)

theorem weakMarkedSet_contains_original {F : (i : ℕ) → Set (Node A i)}
    {N : ℕ} {H : Finset ℕ} {n : ℕ} (hn : n ∈ H) : n ∈ weakMarkedSet F N H :=
  ⟨.inl ⟨n, hn⟩, rfl⟩

theorem weakMarkedSet_contains_meet {F : (i : ℕ) → Set (Node A i)}
    {N : ℕ} {H : Finset ℕ} (hN : N ∈ H) {i : ℕ} {s t : Node A i}
    (hs : s ∈ augmentedFamily F N i) (ht : t ∈ augmentedFamily F N i) :
    s.meetHeight t ∈ weakMarkedSet F N H := by
  classical
  rcases hs with hs | hs
  · rcases ht with ht | ht
    · refine ⟨.inr (.inl (⟨i, ⟨s, hs⟩⟩, ⟨i, ⟨t, ht⟩⟩)), ?_⟩
      simp [weakLevelMark]
    · change t = Node.zero i N at ht
      subst t
      exact ⟨.inr (.inr (.inl ⟨i, ⟨s, hs⟩⟩)), rfl⟩
  · change s = Node.zero i N at hs
    subst s
    rcases ht with ht | ht
    · exact ⟨.inr (.inr (.inr ⟨i, ⟨t, ht⟩⟩)), rfl⟩
    · change t = Node.zero i N at ht
      subst t
      have h := congrArg Node.height (Node.meet_self (Node.zero (A := A) i N))
      rw [Node.height_meet, Node.zero_height] at h
      rw [h]
      exact weakMarkedSet_contains_original hN

theorem weakMarkedSet_le {F : (i : ℕ) → Set (Node A i)}
    {N : ℕ} {H : Finset ℕ} (hH : ∀ n ∈ H, n ≤ N)
    (hF : ∀ i s, s ∈ F i → s.height ≤ N) :
    ∀ n ∈ weakMarkedSet F N H, n ≤ N := by
  classical
  rintro n ⟨q, rfl⟩
  cases q with
  | inl n => exact hH n.val n.property
  | inr q =>
    cases q with
    | inl p =>
      dsimp only [weakLevelMark]
      split_ifs
      · exact (Node.meetHeight_le_left _ _).trans (hF _ _ p.1.2.property)
      · exact le_rfl
    | inr q =>
      cases q with
      | inl s => exact (Node.meetHeight_le_left _ _).trans (hF _ _ s.2.property)
      | inr t => exact (Node.meetHeight_le_right _ _).trans (hF _ _ t.2.property)

theorem weakMarkedSet_finite_card {F : (i : ℕ) → Set (Node A i)}
    {N : ℕ} {H : Finset ℕ} [Finite (FamilyIndex F)] :
    (weakMarkedSet F N H).Finite ∧ Nat.card (weakMarkedSet F N H) ≤
      H.card + (Nat.card (FamilyIndex F)) ^ 2 + 2 * Nat.card (FamilyIndex F) := by
  have hfin := Set.finite_range (weakLevelMark F N H)
  refine ⟨hfin, ?_⟩
  have hc : Nat.card (weakMarkedSet F N H) ≤ Nat.card (WeakLevelIndex F H) :=
    Nat.card_le_card_of_surjective (fun q : WeakLevelIndex F H =>
      (⟨weakLevelMark F N H q, ⟨q, rfl⟩⟩ : weakMarkedSet F N H))
      (by rintro ⟨n, q, rfl⟩; exact ⟨q, rfl⟩)
  refine hc.trans_eq ?_
  simp only [WeakLevelIndex, Nat.card_sum, Nat.card_prod, Nat.card_eq_finsetCard,
    pow_two, two_mul, Nat.add_assoc]

theorem weakMarkedSet_original_trap {F : (i : ℕ) → Set (Node A i)}
    {N : ℕ} {H : Finset ℕ} {O : Set ℕ}
    (hN : N ∈ H) (hheight : ∀ i s, s ∈ F i → s.height ∈ H)
    (hproper : ∀ i (s t : Node A i), s ∈ augmentedFamily F N i →
      t ∈ augmentedFamily F N i → ¬ Node.Prefix s t → ¬ Node.Prefix t s →
      s.meetHeight t ∈ O → s.meetHeight t ∈ H) :
    ∀ n ∈ weakMarkedSet F N H, n ∈ O → n ∈ H := by
  classical
  have hbase : ∀ i s, s ∈ augmentedFamily F N i → s.height ∈ H := by
    intro i s hs
    rcases hs with hs | hs
    · exact hheight i s hs
    · change s = Node.zero i N at hs
      simpa [hs] using hN
  have hpair : ∀ i (s t : Node A i), s ∈ augmentedFamily F N i →
      t ∈ augmentedFamily F N i → s.meetHeight t ∈ O → s.meetHeight t ∈ H := by
    intro i s t hs ht hO
    by_cases hst : Node.Prefix s t
    · have he := congrArg Node.height (Node.meet_eq_left_of_prefix hst)
      rw [Node.height_meet] at he
      rw [he]
      exact hbase i s hs
    · by_cases hts : Node.Prefix t s
      · have he := congrArg Node.height ((Node.meet_comm s t).trans
          (Node.meet_eq_left_of_prefix hts))
        rw [Node.height_meet] at he
        rw [he]
        exact hbase i t ht
      · exact hproper i s t hs ht hst hts hO
  rintro n ⟨q, rfl⟩ hO
  cases q with
  | inl n => exact n.property
  | inr q =>
    cases q with
    | inl p =>
      rcases p with ⟨⟨i, s⟩, ⟨j, t⟩⟩
      by_cases h : i = j
      · subst j
        simpa only [weakLevelMark, dif_pos, cast_eq] using
          (hpair i s.val t.val (Or.inl s.property) (Or.inl t.property) (by
            simpa only [weakLevelMark, dif_pos, cast_eq] using hO))
      · simpa only [weakLevelMark, dif_neg h] using hN
    | inr q =>
      cases q with
      | inl s =>
          exact hpair s.1 s.2.val (Node.zero s.1 N)
            (Or.inl s.2.property) (Or.inr rfl) hO
      | inr t =>
          exact hpair t.1 (Node.zero t.1 N) t.2.val
            (Or.inr rfl) (Or.inl t.2.property) hO

end CombinedRamsey.Positive
