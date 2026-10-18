import CombinedRamsey.Positive.MarkerFamily

/-! Every actual iterated slice is evaluated on its union of slicing coordinates. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

variable (colours : ℕ → ℕ) (c : ∀ v, GenuineColours colours v) (v : ℕ)

theorem cast_alphabet_val {j k : ℕ} (h : j = k) (x : Alphabet colours j) :
    (cast (congrArg (Alphabet colours) h) x).val = x.val := by
  cases h
  rfl

theorem slice_table_val {i : ℕ} (t : Node (Alphabet colours) i) (m : ℕ)
    (h : m < t.height) (s : Coordinate m) :
    ((t.slice m h).table s).val = (t.table (Level.sliceCoordinate h s)).val := by
  have hc : i + (Level.sliceCoordinate h s).val.card = i + 1 + s.val.card := by
    rw [Level.sliceCoordinate_card]
    omega
  exact cast_alphabet_val colours hc _

def mergeCoordinates (P : Finset ℕ) (n : ℕ) (hp : P ⊆ Finset.range (originalHeight colours v))
    (hn : n ≤ originalHeight colours v) (s : Coordinate n) : Coordinate (originalHeight colours v) :=
  ⟨P ∪ s.val, by
    obtain ⟨x, hx⟩ := s.property.1
    exact ⟨x, Finset.mem_union_right _ hx⟩,
    Finset.union_subset hp (s.property.2.trans (Finset.range_mono hn))⟩

structure SliceRecord {i : ℕ} (t : Node (Alphabet colours) i) where
  slicingCoordinates : Finset ℕ
  cardinality : slicingCoordinates.card = i
  bounds : slicingCoordinates ⊆ Finset.range (originalHeight colours v)
  above : ∀ x ∈ slicingCoordinates, t.height ≤ x
  height_bound : t.height ≤ originalHeight colours v
  evaluate : ∀ s : Coordinate t.height,
    (t.table s).val = codeValue colours c v
      (mergeCoordinates colours v slicingCoordinates t.height bounds height_bound s)

namespace SliceRecord

variable {colours c v}

def initial : SliceRecord colours c v (family colours c v) where
  slicingCoordinates := ∅
  cardinality := rfl
  bounds := Finset.empty_subset _
  above := fun _ h => False.elim (Finset.notMem_empty _ h)
  height_bound := le_rfl
  evaluate s := by
    apply congrArg (codeValue colours c v)
    apply Subtype.ext
    simp [mergeCoordinates]

def next {i : ℕ} {t : Node (Alphabet colours) i} (w : SliceRecord colours c v t)
    (n : ℕ) (hn : n < t.height) : SliceRecord colours c v (t.slice n hn) := by
  have hnp : n ∉ w.slicingCoordinates := by
    intro hp
    have := w.above n hp
    omega
  have hp : insert n w.slicingCoordinates ⊆ Finset.range (originalHeight colours v) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr (hn.trans_le w.height_bound)
    · exact w.bounds hx
  refine {
    slicingCoordinates := insert n w.slicingCoordinates
    cardinality := by rw [Finset.card_insert_of_notMem hnp, w.cardinality]
    bounds := hp
    above := ?_
    height_bound := hn.le.trans w.height_bound
    evaluate := ?_ }
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact hn.le.trans (w.above x hx)
  · intro s
    rw [slice_table_val, w.evaluate]
    apply congrArg (codeValue colours c v)
    apply Subtype.ext
    simp [mergeCoordinates, Level.sliceCoordinate, Finset.union_insert]

theorem zero_of_marker_prefix {i : ℕ} {t : Node (Alphabet colours) i} (w : SliceRecord colours c v t)
    (p : ℕ) (hp : p ∈ w.slicingCoordinates) (hD : p ∈ markerPositions colours) :
    t = Node.zero i t.height := by
  cases t with
  | mk n table =>
    apply congrArg (Node.mk n)
    funext s
    apply Fin.ext
    have he := w.evaluate s
    have hz : codeValue colours c v (mergeCoordinates colours v w.slicingCoordinates n
        w.bounds w.height_bound s) = 0 := by
      obtain ⟨q, hq⟩ := s.property.1
      apply codeValue_zero_of_marker_not_minimum colours c _ p q
      · exact Finset.mem_union_left _ hp
      · exact hD
      · exact Finset.mem_union_right _ hq
      · exact (Finset.mem_range.mp (s.property.2 hq)).trans_le (w.above p hp)
    exact he.trans hz

end SliceRecord

inductive IteratedSlice : (i : ℕ) → Node (Alphabet colours) i → Prop where
  | initial : IteratedSlice 0 (family colours c v)
  | step {i : ℕ} {t : Node (Alphabet colours) i} (h : IteratedSlice i t)
      (n : ℕ) (hn : n < t.height) : IteratedSlice (i + 1) (t.slice n hn)

theorem iterated_slice_record {i : ℕ} {t : Node (Alphabet colours) i}
    (h : IteratedSlice colours c v i t) : Nonempty (SliceRecord colours c v t) := by
  induction h with
  | initial => exact ⟨SliceRecord.initial⟩
  | step _ n hn ih => exact ⟨(Classical.choice ih).next n hn⟩

theorem slice_at_marker_zero {i : ℕ} {t : Node (Alphabet colours) i}
    (h : IteratedSlice colours c v i t) (n : ℕ) (hn : n < t.height)
    (hD : n ∈ markerPositions colours) : t.slice n hn = Node.zero (i + 1) n := by
  obtain ⟨w⟩ := iterated_slice_record colours c v h
  exact (w.next n hn).zero_of_marker_prefix n (Finset.mem_insert_self _ _) hD

end CombinedRamsey.Positive.Marker


