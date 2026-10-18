import RelationalRamsey632.Coding.Separation
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The finite level envelope: off-diagonal library pairs contribute their meet;
diagonal pairs contribute the last zero restriction.  This is the exact
`choose(n,2)+n=choose(n+1,2)` count in the paper.
-/

namespace RelationalRamsey632.Coding

open Source
open scoped Classical

variable {A : ℕ → Type} [∀ j, Zero (A j)]

noncomputable def pairMarker {i : ℕ} (G : Set (Node A i)) : Sym2 G → ℕ := by
  classical
  exact Sym2.lift ⟨fun s t => if s = t then s.val.zeroBoundary else s.val.meetHeight t.val,
    by
      intro s t
      by_cases h : s = t
      · subst t
        rfl
      · simp only [if_neg h, if_neg (Ne.symm h)]
        exact congrArg Node.height (Node.meet_comm s.val t.val)⟩

@[simp] theorem pairMarker_mk {i : ℕ} (G : Set (Node A i)) (s t : G) :
    pairMarker G (Sym2.mk s t) =
      if s = t then s.val.zeroBoundary else s.val.meetHeight t.val := rfl

abbrev MarkerIndex (X : Set (Node A 0)) (H : Finset ℕ) (m : ℕ) :=
  H ⊕ ((i : Fin m) × Sym2 (sliceLibrary A X H i.val))

noncomputable def markerLevel (X : Set (Node A 0)) (H : Finset ℕ) (m : ℕ) :
    MarkerIndex X H m → ℕ
  | Sum.inl h => h.val
  | Sum.inr ⟨_, p⟩ => pairMarker _ p

def markedLevels (X : Set (Node A 0)) (H : Finset ℕ) (m : ℕ) : Set ℕ :=
  Set.range (markerLevel X H m)

def levelBound (m : ℕ) : ℕ :=
  m + ∑ i : Fin m, Nat.choose (m ^ (i.val + 1) + 1) 2

theorem original_mem_markedLevels {X : Set (Node A 0)} {H : Finset ℕ} {m n : ℕ}
    (hn : n ∈ H) : n ∈ markedLevels X H m := ⟨Sum.inl ⟨n, hn⟩, rfl⟩

theorem markedLevels_finite_card {X : Set (Node A 0)} {H : Finset ℕ}
    (hX : X.Finite) (hH : H.card ≤ Nat.card X) :
    (markedLevels X H (Nat.card X)).Finite ∧
      Nat.card (markedLevels X H (Nat.card X)) ≤ levelBound (Nat.card X) := by
  classical
  let m := Nat.card X
  haveI : ∀ i : Fin m, Finite (sliceLibrary A X H i.val) :=
    fun i => (sliceLibrary_finite_card A X H hX i.val).1.to_subtype
  letI : ∀ i : Fin m, Fintype (sliceLibrary A X H i.val) := fun _ => Fintype.ofFinite _
  haveI : Finite (MarkerIndex X H m) := inferInstance
  have hf : (markedLevels X H m).Finite := Set.finite_range (markerLevel X H m)
  refine ⟨hf, ?_⟩
  have hcard : Nat.card (markedLevels X H m) ≤ Nat.card (MarkerIndex X H m) :=
    Nat.card_le_card_of_surjective (fun q : MarkerIndex X H m =>
      (⟨markerLevel X H m q, ⟨q, rfl⟩⟩ : markedLevels X H m))
      (by rintro ⟨n, q, rfl⟩; exact ⟨q, rfl⟩)
  apply hcard.trans
  change Nat.card (H ⊕ ((i : Fin m) × Sym2 (sliceLibrary A X H i.val))) ≤ _
  rw [Nat.card_sum, Nat.card_sigma, Nat.card_eq_finsetCard]
  apply Nat.add_le_add hH
  apply Finset.sum_le_sum
  intro i _
  letI := Fintype.ofFinite (sliceLibrary A X H i.val)
  rw [Nat.card_eq_fintype_card, Sym2.card]
  apply Nat.choose_le_choose 2
  simpa only [Fintype.card_eq_nat_card] using
    Nat.add_le_add_right (sliceLibrary_card_power A X H hX hH i.val) 1

theorem library_zeroBoundary_mem {X : Set (Node A 0)} {H : Finset ℕ} {m i : ℕ}
    (hi : i < m) {t : Node A i} (ht : t ∈ sliceLibrary A X H i) :
    t.zeroBoundary ∈ markedLevels X H m := by
  classical
  refine ⟨Sum.inr ⟨⟨i, hi⟩, Sym2.mk ⟨t, ht⟩ ⟨t, ht⟩⟩, ?_⟩
  simp [markerLevel]

theorem library_meetHeight_mem {X : Set (Node A 0)} {H : Finset ℕ} {m i : ℕ}
    (hi : i < m) (hheights : ∀ s ∈ X, s.height ∈ H)
    {s t : Node A i} (hs : s ∈ sliceLibrary A X H i) (ht : t ∈ sliceLibrary A X H i) :
    s.meetHeight t ∈ markedLevels X H m := by
  classical
  by_cases he : s = t
  · subst t
    have hh := sliceLibrary_height A X H hheights hs
    have hm := congrArg Node.height (Node.meet_self s)
    rw [Node.height_meet] at hm
    exact hm.symm ▸ original_mem_markedLevels hh
  · refine ⟨Sum.inr ⟨⟨i, hi⟩, Sym2.mk ⟨s, hs⟩ ⟨t, ht⟩⟩, ?_⟩
    have hst : (⟨s, hs⟩ : sliceLibrary A X H i) ≠ ⟨t, ht⟩ := by
      intro h
      exact he (congrArg Subtype.val h)
    simp [markerLevel, hst]

theorem marked_originals {R X : Set (Node A 0)} {O : Set ℕ} {H : Finset ℕ} {m : ℕ}
    (hsep : SeparatedAtAllDepths R O) (hXR : X ⊆ R)
    (hheights : ∀ s ∈ X, s.height ∈ H) :
    ∀ n ∈ markedLevels X H m, n ∈ O → n ∈ H := by
  classical
  rintro n ⟨q, rfl⟩ hn
  cases q with
  | inl h => exact h.property
  | inr p =>
    rcases p with ⟨i, p⟩
    refine Sym2.ind (fun s t => ?_) p hn
    intro hO
    change pairMarker (sliceLibrary A X H i.val) (Sym2.mk s t) ∈ O at hO
    change pairMarker (sliceLibrary A X H i.val) (Sym2.mk s t) ∈ H
    by_cases he : s = t
    · have hmark : pairMarker (sliceLibrary A X H i.val) (Sym2.mk s t) = s.val.zeroBoundary := by
        simp [he]
      rw [hmark] at hO ⊢
      by_cases hz : s.val = Node.zero i.val s.val.height
      · have hb := (Node.zeroBoundary_eq_height_iff s.val).mpr hz
        rw [hb]
        exact sliceLibrary_height A X H hheights s.property
      · exact False.elim ((library_zeroBoundary_not_original hsep hXR s.property hz) hO)
    · have hmark : pairMarker (sliceLibrary A X H i.val) (Sym2.mk s t) = s.val.meetHeight t.val := by
        simp [he]
      rw [hmark] at hO ⊢
      by_cases hst : Node.Prefix s.val t.val
      · have hm := congrArg Node.height (Node.meet_eq_left_of_prefix hst)
        rw [Node.height_meet] at hm
        rw [hm]
        exact sliceLibrary_height A X H hheights s.property
      · by_cases hts : Node.Prefix t.val s.val
        · have hm := congrArg Node.height ((Node.meet_comm s.val t.val).trans
            (Node.meet_eq_left_of_prefix hts))
          rw [Node.height_meet] at hm
          rw [hm]
          exact sliceLibrary_height A X H hheights t.property
        · exact False.elim (hsep.proper_meet i.val s.val t.val
            (Or.inl (library_descendant hXR s.property))
            (Or.inl (library_descendant hXR t.property)) hst hts hO)

end RelationalRamsey632.Coding

