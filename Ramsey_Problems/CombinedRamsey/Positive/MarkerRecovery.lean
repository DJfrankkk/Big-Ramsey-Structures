import CombinedRamsey.Positive.MarkerOriginalSlices

/-! Genuine colours are recovered by the reserved singleton markers when depth <= n. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

variable (colours : ℕ → ℕ)

def supportTail {n : ℕ} (R : Coordinate (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x.val ∈ R.val)

theorem supportTail_support {n : ℕ} (R : Coordinate (n + 1)) (hn : n ∈ R.val) :
    insert n ((supportTail R).image Fin.val) = R.val := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hn
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
  · intro hx
    by_cases hxn : x = n
    · exact hxn.symm ▸ Finset.mem_insert_self _ _
    · have hlt : x < n := by
        have := Finset.mem_range.mp (R.property.2 hx)
        omega
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨⟨x, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩)

theorem supportTail_card {n : ℕ} (R : Coordinate (n + 1)) (hn : n ∈ R.val) :
    (supportTail R).card + 1 = R.val.card := by
  have hnot : n ∉ (supportTail R).image Fin.val := by
    intro h
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp h
    have := i.isLt
    omega
  have hc := congrArg Finset.card (supportTail_support R hn)
  simpa only [Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ Fin.val_injective] using hc

def markerForSupport {n i : ℕ} (R : Coordinate (n + 1)) (hn : n ∈ R.val)
    (hi : i ≤ n) (s : ℕ) (hs : 0 < s) (hbound : s ≤ colours (i + R.val.card)) :
    Block colours n :=
  ⟨supportTail R, ⟨s - 1, by
    have hc := colour_le_cutoff colours (r := R.val.card) hi
    have hc' := hc.trans_eq (congrArg (cutoff colours n) (supportTail_card R hn)).symm
    omega⟩⟩

@[simp] theorem markerForSupport_colour {n i : ℕ} (R : Coordinate (n + 1)) (hn : n ∈ R.val)
    (hi : i ≤ n) (s : ℕ) (hs : 0 < s) (hbound : s ≤ colours (i + R.val.card)) :
    (markerForSupport colours R hn hi s hs hbound).2.val + 1 = s := by
  dsimp [markerForSupport]
  omega

theorem markerForSupport_suffix {n i : ℕ} (R : Coordinate (n + 1)) (hn : n ∈ R.val)
    (hi : i ≤ n) (s : ℕ) (hs : 0 < s) (hbound : s ≤ colours (i + R.val.card)) :
    suffix colours (markerForSupport colours R hn hi s hs hbound) = R.val :=
  supportTail_support R hn

namespace OriginalSliceRecord

variable {colours} {c : ∀ v, GenuineColours colours v} {v i : ℕ} {t : Node (Alphabet colours) i}

def remainderProfile (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (R : Coordinate (n + 1)) : Coordinate v :=
  ⟨w.originalPrefix ∪ R.val, by
    obtain ⟨x, hx⟩ := R.property.1
    exact ⟨x, Finset.mem_union_right _ hx⟩, by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_range.mpr (w.prefix_lt hx)
    · have hle : x ≤ n := by have := Finset.mem_range.mp (R.property.2 hx); omega
      exact Finset.mem_range.mpr (hle.trans_lt (w.origin_above habove))⟩

theorem remainder_disjoint (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (R : Coordinate (n + 1)) :
    Disjoint w.originalPrefix R.val := by
  apply Finset.disjoint_left.mpr
  intro x hp hR
  have h1 := w.prefix_above_original habove hp
  have h2 := Finset.mem_range.mp (R.property.2 hR)
  omega

theorem remainderProfile_card (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (R : Coordinate (n + 1)) :
    (w.remainderProfile habove R).val.card = i + R.val.card := by
  rw [remainderProfile, Finset.card_union_of_disjoint (w.remainder_disjoint habove R), w.cardinality]

def singletonMarkerWitness (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (hi : i ≤ n) (b : Block colours n) :
    MarkerWitness colours v
      (mergeCoordinates colours v w.record.slicingCoordinates t.height w.record.bounds w.record.height_bound
        (Level.singletonCoordinate ((markerPosition_lt_original colours b).trans habove))) where
  marker := ⟨n, b⟩
  originalPrefix := w.originalPrefix
  marker_lt := w.origin_above habove
  prefix_lt := fun _ hx => w.prefix_lt hx
  prefix_gt := fun _ hx => w.prefix_above_original habove hx
  depth_bound := by simpa only [w.cardinality] using hi
  coordinates_eq := by
    change w.record.slicingCoordinates ∪ {markerPosition colours b} =
      insert (markerPosition colours b) (w.originalPrefix.image (originalHeight colours))
    rw [← w.image_eq]
    simp only [Finset.union_singleton]

theorem singleton_marker_value (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (hi : i ≤ n) (b : Block colours n) :
    (t.table (Level.singletonCoordinate ((markerPosition_lt_original colours b).trans habove))).val =
      if (c v (w.singletonMarkerWitness habove hi b).fullSupport).val = b.2.val + 1
      then colours (i + 1) + 1 else 0 := by
  let d := w.singletonMarkerWitness habove hi b
  have hd := marker_value colours c d
  have hc : (mergeCoordinates colours v w.record.slicingCoordinates t.height w.record.bounds
      w.record.height_bound
      (Level.singletonCoordinate ((markerPosition_lt_original colours b).trans habove))).val.card = i + 1 :=
    d.coordinate_card.trans (congrArg (fun a => a + 1) w.cardinality)
  rw [w.record.evaluate]
  change codeValue colours c v _ = _
  change codeValue colours c v _ = _ at hd
  rw [hd, hc]
  rfl

theorem recovered_marker (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (hi : i ≤ n)
    (R : Coordinate (n + 1)) (hn : n ∈ R.val)
    (s : ℕ) (hs : 0 < s) (hbound : s ≤ colours (i + R.val.card)) :
    (t.table (Level.singletonCoordinate
      ((markerPosition_lt_original colours (markerForSupport colours R hn hi s hs hbound)).trans habove))).val =
      if (c v (w.remainderProfile habove R)).val = s then colours (i + 1) + 1 else 0 := by
  have hprofile : (w.singletonMarkerWitness habove hi
      (markerForSupport colours R hn hi s hs hbound)).fullSupport = w.remainderProfile habove R := by
    apply Subtype.ext
    exact congrArg (fun S => w.originalPrefix ∪ S) (markerForSupport_suffix colours R hn hi s hs hbound)
  rw [w.singleton_marker_value habove hi (markerForSupport colours R hn hi s hs hbound), hprofile,
    markerForSupport_colour]

theorem remainder_color_le (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (habove : originalHeight colours n < t.height) (R : Coordinate (n + 1)) :
    (c v (w.remainderProfile habove R)).val ≤ colours (i + R.val.card) := by
  have h := (c v (w.remainderProfile habove R)).isLt
  have hc := congrArg (fun r => colours r + 1) (w.remainderProfile_card habove R)
  have h' := h.trans_le hc.le
  omega

end OriginalSliceRecord
end CombinedRamsey.Positive.Marker
