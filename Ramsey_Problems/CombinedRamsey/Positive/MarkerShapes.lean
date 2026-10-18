import CombinedRamsey.Positive.MarkerAgreement

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

variable (colours : ℕ → ℕ)

inductive CoordinateShape (i n : ℕ) (C : Finset ℕ) : Prop where
  | original (R : Coordinate (n + 1)) (top : n ∈ R.val)
      (coordinates : C = R.val.image (originalHeight colours)) : CoordinateShape i n C
  | marker (beta : Sigma (Block colours)) (originalPart : Finset ℕ)
      (marker_le : beta.1 ≤ n) (part_le : ∀ x ∈ originalPart, x ≤ n)
      (part_gt : ∀ x ∈ originalPart, beta.1 < x) (top : n ∈ originalPart)
      (depth : i + originalPart.card ≤ beta.1)
      (coordinates : C = insert (allMarkerPosition colours beta)
        (originalPart.image (originalHeight colours))) : CoordinateShape i n C

def markerRemainder {n : ℕ} (beta : Sigma (Block colours)) (P : Finset ℕ)
    (hb : beta.1 ≤ n) (hP : ∀ x ∈ P, x ≤ n) : Coordinate (n + 1) :=
  ⟨P ∪ suffix colours beta.2, by
    obtain ⟨x, hx⟩ := suffix_nonempty colours beta.2
    exact ⟨x, Finset.mem_union_right _ hx⟩, by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_range.mpr (by have := hP x hx; omega)
    · exact Finset.mem_range.mpr (by have := (suffix_le colours beta.2 hx).trans hb; omega)⟩

namespace OriginalSliceRecord

variable {colours} {c : ∀ v, GenuineColours colours v} {v i : ℕ} {t : Node (Alphabet colours) i}

theorem local_coordinate_disjoint (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (C : Coordinate (originalHeight colours n + 1)) :
    Disjoint w.record.slicingCoordinates C.val := by
  apply Finset.disjoint_left.mpr
  intro x hp hC
  have ha := w.record.above x hp
  have hc := Finset.mem_range.mp (C.property.2 hC)
  omega

theorem merged_local_card (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (C : Coordinate (originalHeight colours n + 1)) :
    (mergeCoordinates colours v w.record.slicingCoordinates t.height w.record.bounds
      w.record.height_bound (C.inclusion (by omega))).val.card = i + C.val.card := by
  change (w.record.slicingCoordinates ∪ C.val).card = i + C.val.card
  rw [Finset.card_union_of_disjoint (w.local_coordinate_disjoint habove C), w.record.cardinality]

theorem original_shape_value (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (C : Coordinate (originalHeight colours n + 1))
    (R : Coordinate (n + 1)) (hC : C.val = R.val.image (originalHeight colours)) :
    (t.table (C.inclusion (by omega))).val = (c v (w.remainderProfile habove R)).val := by
  have hcoord : mergeCoordinates colours v w.record.slicingCoordinates t.height w.record.bounds
      w.record.height_bound (C.inclusion (by omega)) = mapOriginal colours (w.remainderProfile habove R) := by
    apply Subtype.ext
    change w.record.slicingCoordinates ∪ C.val =
      (w.originalPrefix ∪ R.val).image (originalHeight colours)
    rw [← w.image_eq, hC, Finset.image_union]
  rw [w.record.evaluate, hcoord]
  exact original_value colours c (w.remainderProfile habove R)

theorem marker_shape_value (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (C : Coordinate (originalHeight colours n + 1))
    (beta : Sigma (Block colours)) (P : Finset ℕ) (hb : beta.1 ≤ n)
    (hP : ∀ x ∈ P, x ≤ n) (hgt : ∀ x ∈ P, beta.1 < x)
    (hdepth : i + P.card ≤ beta.1)
    (hC : C.val = insert (allMarkerPosition colours beta) (P.image (originalHeight colours))) :
    (t.table (C.inclusion (by omega))).val =
      if (c v (w.remainderProfile habove (markerRemainder colours beta P hb hP))).val = beta.2.2.val + 1
      then colours (i + C.val.card) + 1 else 0 := by
  let M := mergeCoordinates colours v w.record.slicingCoordinates t.height w.record.bounds
    w.record.height_bound (C.inclusion (by omega))
  let d : MarkerWitness colours v M := {
    marker := beta
    originalPrefix := w.originalPrefix ∪ P
    marker_lt := hb.trans_lt (w.origin_above habove)
    prefix_lt := fun x hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact w.prefix_lt hx
      · exact (hP x hx).trans_lt (w.origin_above habove)
    prefix_gt := fun x hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hb.trans_lt (w.prefix_above_original habove hx)
      · exact hgt x hx
    depth_bound := by
      apply (Finset.card_union_le _ _).trans
      simpa only [w.cardinality] using hdepth
    coordinates_eq := by
      change w.record.slicingCoordinates ∪ C.val =
        insert (allMarkerPosition colours beta) ((w.originalPrefix ∪ P).image (originalHeight colours))
      rw [← w.image_eq, hC, Finset.image_union, Finset.union_insert] }
  have hprofile : d.fullSupport = w.remainderProfile habove (markerRemainder colours beta P hb hP) := by
    apply Subtype.ext
    exact Finset.union_assoc _ _ _
  have hd := marker_value colours c d
  change codeValue colours c v M = _ at hd
  rw [w.record.evaluate]
  change codeValue colours c v M = _
  rw [hd, w.merged_local_card habove C, hprofile]

end OriginalSliceRecord

theorem coordinate_shape_agreement {c : ∀ v, GenuineColours colours v}
    {i v w n : ℕ} {s t : Node (Alphabet colours) i}
    (S : OriginalSliceRecord colours c v s) (T : OriginalSliceRecord colours c w t)
    (hs : originalHeight colours n < s.height) (ht : originalHeight colours n < t.height)
    (hi : i ≤ n) (hcommon : Node.CommonHeight s t (originalHeight colours n))
    (C : Coordinate (originalHeight colours n + 1)) (hshape : CoordinateShape colours i n C.val) :
    (s.table (C.inclusion (by omega))).val = (t.table (C.inclusion (by omega))).val := by
  cases hshape with
  | original R hn hC =>
    rw [S.original_shape_value hs C R hC, T.original_shape_value ht C R hC]
    exact remainder_colors_equal S T hs ht hi hcommon R hn
  | marker beta P hb hP hgt hn hdepth hC =>
    rw [S.marker_shape_value hs C beta P hb hP hgt hdepth hC,
      T.marker_shape_value ht C beta P hb hP hgt hdepth hC,
      remainder_colors_equal S T hs ht hi hcommon (markerRemainder colours beta P hb hP)
        (Finset.mem_union_left _ hn)]

theorem coordinate_shape_zero {c : ∀ v, GenuineColours colours v}
    {i v n m : ℕ} {s : Node (Alphabet colours) i}
    (S : OriginalSliceRecord colours c v s)
    (hs : originalHeight colours n < s.height) (hm : originalHeight colours n < m)
    (hi : i ≤ n) (hcommon : Node.CommonHeight s (Node.zero i m) (originalHeight colours n))
    (C : Coordinate (originalHeight colours n + 1)) (hshape : CoordinateShape colours i n C.val) :
    (s.table (C.inclusion (by omega))).val = 0 := by
  cases hshape with
  | original R hn hC =>
    rw [S.original_shape_value hs C R hC]
    exact remainder_color_zero S hs hm hi hcommon R hn
  | marker beta P hb hP hgt hn hdepth hC =>
    rw [S.marker_shape_value hs C beta P hb hP hgt hdepth hC,
      remainder_color_zero S hs hm hi hcommon (markerRemainder colours beta P hb hP)
        (Finset.mem_union_left _ hn)]
    simp

end CombinedRamsey.Positive.Marker
