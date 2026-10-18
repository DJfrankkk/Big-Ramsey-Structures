import RelationalRamsey632.Source.Meets
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Intrinsic generated closure

The inductive derivations insert exactly the operations in the article.
There is no generator for a root, a zero node, or any other constant.
-/

namespace RelationalRamsey632.Source

variable (A : ℕ → Type)

abbrev SourceObject := (Sigma (Node A)) ⊕ ℕ

namespace SourceObject

def weight (x : SourceObject A) : ℕ :=
  match x with
  | Sum.inl ⟨i, t⟩ => i + t.height
  | Sum.inr n => n

end SourceObject

inductive Generated (X : Set (Node A 0)) : SourceObject A → Prop where
  | generator (t : Node A 0) (h : t ∈ X) : Generated X (.inl ⟨0, t⟩)
  | height {i : ℕ} (t : Node A i)
      (h : Generated X (.inl ⟨i, t⟩)) : Generated X (.inr t.height)
  | meet {i : ℕ} (s t : Node A i)
      (hs : Generated X (.inl ⟨i, s⟩))
      (ht : Generated X (.inl ⟨i, t⟩)) :
      Generated X (.inl ⟨i, s.meet t⟩)
  | restrict {i : ℕ} (t : Node A i) (n : ℕ)
      (ht : Generated X (.inl ⟨i, t⟩))
      (hn : Generated X (.inr n)) (h : n ≤ t.height) :
      Generated X (.inl ⟨i, t.restrict n h⟩)
  | slice {i : ℕ} (t : Node A i) (n : ℕ)
      (ht : Generated X (.inl ⟨i, t⟩))
      (hn : Generated X (.inr n)) (h : n < t.height) :
      Generated X (.inl ⟨i + 1, t.slice n h⟩)

def closureNodes (X : Set (Node A 0)) (i : ℕ) : Set (Node A i) :=
  {t | Generated A X (.inl ⟨i, t⟩)}

def closureLevels (X : Set (Node A 0)) : Set ℕ :=
  {n | Generated A X (.inr n)}

theorem closureLevels_node_witness {X : Set (Node A 0)} {n : ℕ}
    (hn : n ∈ closureLevels A X) :
    ∃ i, ∃ t : Node A i, t ∈ closureNodes A X i ∧ t.height = n := by
  cases hn with
  | height t ht => exact ⟨_, t, ht, rfl⟩

structure Closed (E : (i : ℕ) → Set (Node A i)) (L : Set ℕ) : Prop where
  height : ∀ i t, t ∈ E i → t.height ∈ L
  meet : ∀ i s t, s ∈ E i → t ∈ E i → s.meet t ∈ E i
  restrict : ∀ i t n, t ∈ E i → n ∈ L → ∀ h : n ≤ t.height, t.restrict n h ∈ E i
  slice : ∀ i t n, t ∈ E i → n ∈ L → ∀ h : n < t.height, t.slice n h ∈ E (i + 1)

theorem generatedClosure_closed (X : Set (Node A 0)) :
    Closed A (closureNodes A X) (closureLevels A X) where
  height := fun _ t h => Generated.height t h
  meet := fun _ s t hs ht => Generated.meet s t hs ht
  restrict := fun _ t n ht hn h => Generated.restrict t n ht hn h
  slice := fun _ t n ht hn h => Generated.slice t n ht hn h

theorem generator_mem (X : Set (Node A 0)) {t : Node A 0} (h : t ∈ X) :
    t ∈ closureNodes A X 0 := Generated.generator t h

theorem generatedClosure_least (X : Set (Node A 0))
    (E : (i : ℕ) → Set (Node A i)) (L : Set ℕ)
    (hclosed : Closed A E L) (hX : X ⊆ E 0) :
    (∀ i, closureNodes A X i ⊆ E i) ∧ closureLevels A X ⊆ L := by
  have transport : ∀ x, Generated A X x →
      (match x with | .inl ⟨i, t⟩ => t ∈ E i | .inr n => n ∈ L) := by
    intro x h
    induction h with
    | generator t ht => exact hX ht
    | height t ht ih => exact hclosed.height _ t ih
    | meet s t hs ht ihs iht => exact hclosed.meet _ s t ihs iht
    | restrict t n ht hn h iht ihn => exact hclosed.restrict _ t n iht ihn h
    | slice t n ht hn h iht ihn => exact hclosed.slice _ t n iht ihn h
  exact ⟨fun i t ht => transport _ ht, fun n hn => transport _ hn⟩

theorem generated_mono {X Y : Set (Node A 0)} (hXY : X ⊆ Y) :
    ∀ x, Generated A X x → Generated A Y x := by
  intro x hx
  induction hx with
  | generator t h => exact Generated.generator t (hXY h)
  | height t ht ih => exact Generated.height t ih
  | meet s t hs ht ihs iht => exact Generated.meet s t ihs iht
  | restrict t n ht hn h iht ihn => exact Generated.restrict t n iht ihn h
  | slice t n ht hn h iht ihn => exact Generated.slice t n iht ihn h

theorem generated_weight_bound {X : Set (Node A 0)} {H : ℕ}
    (hX : ∀ t ∈ X, t.height ≤ H) :
    ∀ x, Generated A X x → SourceObject.weight A x ≤ H := by
  intro x hx
  induction hx with
  | generator t h => simpa [SourceObject.weight] using hX t h
  | height t ht ih =>
    dsimp [SourceObject.weight] at ih ⊢
    omega
  | meet s t hs ht ihs iht =>
    dsimp [SourceObject.weight] at ihs iht ⊢
    have h := Node.meetHeight_le_left s t
    omega
  | restrict t n ht hn h iht ihn =>
    dsimp [SourceObject.weight] at iht ihn ⊢
    omega
  | slice t n ht hn h iht ihn =>
    dsimp [SourceObject.weight] at iht ihn ⊢
    omega

theorem closure_node_bound {X : Set (Node A 0)} {H : ℕ}
    (hX : ∀ t ∈ X, t.height ≤ H) {i : ℕ} {t : Node A i}
    (ht : t ∈ closureNodes A X i) : i + t.height ≤ H :=
  generated_weight_bound A hX _ ht

theorem closure_level_bound {X : Set (Node A 0)} {H : ℕ}
    (hX : ∀ t ∈ X, t.height ≤ H) {n : ℕ}
    (hn : n ∈ closureLevels A X) : n ≤ H :=
  generated_weight_bound A hX _ hn

theorem closure_high_sort_empty {X : Set (Node A 0)} {H i : ℕ}
    (hX : ∀ t ∈ X, t.height ≤ H) (hi : H < i) :
    closureNodes A X i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := closure_node_bound A hX ht
  omega

theorem finite_height_nodes [∀ j, Fintype (A j)] (i H : ℕ) :
    {t : Node A i | t.height ≤ H}.Finite := by
  let decode : (Σ n : Fin (H + 1), Level A i n.val) → Node A i :=
    fun p => ⟨p.1.val, p.2⟩
  apply (Set.finite_range decode).subset
  intro t ht
  change t.height ≤ H at ht
  exact ⟨⟨⟨t.height, by omega⟩, t.table⟩, rfl⟩

theorem closureNodes_finite [∀ j, Fintype (A j)]
    {X : Set (Node A 0)} {H : ℕ} (hX : ∀ t ∈ X, t.height ≤ H) (i : ℕ) :
    (closureNodes A X i).Finite := by
  apply (finite_height_nodes A i H).subset
  intro t ht
  change t.height ≤ H
  have h := closure_node_bound A hX ht
  omega

theorem closureLevels_finite {X : Set (Node A 0)} {H : ℕ}
    (hX : ∀ t ∈ X, t.height ≤ H) : (closureLevels A X).Finite := by
  apply (Finset.finite_toSet (Finset.range (H + 1))).subset
  intro n hn
  exact Finset.mem_range.mpr (by have h := closure_level_bound A hX hn; omega)

theorem generated_finite_of_height_bound [∀ j, Fintype (A j)]
    {X : Set (Node A 0)} {H : ℕ} (hX : ∀ t ∈ X, t.height ≤ H) :
    {x : SourceObject A | Generated A X x}.Finite := by
  have hNodes :
      {p : Sigma (Node A) | Generated A X (.inl p)}.Finite := by
    have hfin := Set.finite_iUnion
      (fun i : Fin (H + 1) =>
        (closureNodes_finite A hX i.val).image
          (fun t : Node A i.val => (⟨i.val, t⟩ : Sigma (Node A))))
    apply hfin.subset
    rintro ⟨i, t⟩ ht
    have hbound := closure_node_bound A hX ht
    exact Set.mem_iUnion.mpr
      ⟨⟨i, by omega⟩, ⟨t, ht, rfl⟩⟩
  apply ((hNodes.image Sum.inl).union
    ((closureLevels_finite A hX).image Sum.inr)).subset
  intro x hx
  cases x with
  | inl p => exact Or.inl ⟨p, hx, rfl⟩
  | inr n => exact Or.inr ⟨n, hx, rfl⟩

/-- All-sort finiteness of the least closure, for every finite generator set. -/
theorem generated_finite [∀ j, Fintype (A j)] {X : Set (Node A 0)}
    (hX : X.Finite) : {x : SourceObject A | Generated A X x}.Finite := by
  classical
  apply generated_finite_of_height_bound A
    (H := hX.toFinset.sup Node.height)
  intro t ht
  exact Finset.le_sup (f := Node.height) (hX.mem_toFinset.mpr ht)

end RelationalRamsey632.Source
