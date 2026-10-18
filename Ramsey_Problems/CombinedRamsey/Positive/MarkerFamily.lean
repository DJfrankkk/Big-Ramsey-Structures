import CombinedRamsey.Positive.MarkerBlocks
import RelationalRamsey632.Coding.ZeroNodes

/-! The actual reserved-marker node family in the unchanged valuation alphabet. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

variable (colours : ℕ → ℕ)

abbrev GenuineColours (v : ℕ) := (s : Coordinate v) → Fin (colours s.val.card + 1)

def mapOriginal {v : ℕ} (s : Coordinate v) : Coordinate (originalHeight colours v) :=
  ⟨s.val.image (originalHeight colours), s.property.1.image _, by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr
      ((originalHeight_strictMono colours) (Finset.mem_range.mp (s.property.2 hx)))⟩

@[simp] theorem mapOriginal_card {v : ℕ} (s : Coordinate v) :
    (mapOriginal colours s).val.card = s.val.card :=
  Finset.card_image_of_injective _ (originalHeight_strictMono colours).injective

structure OriginalWitness (v : ℕ) (t : Coordinate (originalHeight colours v)) where
  support : Coordinate v
  image_eq : support.val.image (originalHeight colours) = t.val

instance originalWitnessSubsingleton (v : ℕ) (t : Coordinate (originalHeight colours v)) :
    Subsingleton (OriginalWitness colours v t) := by
  refine ⟨fun s u => ?_⟩
  have hs : s.support = u.support := by
    apply Subtype.ext
    exact Finset.image_injective (originalHeight_strictMono colours).injective
      (s.image_eq.trans u.image_eq.symm)
  cases s
  cases u
  cases hs
  rfl

structure MarkerWitness (v : ℕ) (t : Coordinate (originalHeight colours v)) where
  marker : Sigma (Block colours)
  originalPrefix : Finset ℕ
  marker_lt : marker.1 < v
  prefix_lt : ∀ x ∈ originalPrefix, x < v
  prefix_gt : ∀ x ∈ originalPrefix, marker.1 < x
  depth_bound : originalPrefix.card ≤ marker.1
  coordinates_eq : t.val = insert (allMarkerPosition colours marker)
    (originalPrefix.image (originalHeight colours))

namespace MarkerWitness

variable {colours} {v : ℕ} {t : Coordinate (originalHeight colours v)}

def fullSupport (w : MarkerWitness colours v t) : Coordinate v :=
  ⟨w.originalPrefix ∪ suffix colours w.marker.2, by
    obtain ⟨x, hx⟩ := suffix_nonempty colours w.marker.2
    exact ⟨x, Finset.mem_union_right _ hx⟩, by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_range.mpr (w.prefix_lt x hx)
    · exact Finset.mem_range.mpr ((suffix_le colours w.marker.2 hx).trans_lt w.marker_lt)⟩

theorem marker_not_in_original_image (w : MarkerWitness colours v t) :
    allMarkerPosition colours w.marker ∉ w.originalPrefix.image (originalHeight colours) := by
  rintro hm
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
  exact markerPosition_ne_original colours w.marker.2 x hx.symm

theorem coordinate_card (w : MarkerWitness colours v t) : t.val.card = w.originalPrefix.card + 1 := by
  rw [w.coordinates_eq, Finset.card_insert_of_notMem w.marker_not_in_original_image]
  rw [Finset.card_image_of_injective _ (originalHeight_strictMono colours).injective]

theorem marker_in_coordinates (w : MarkerWitness colours v t) :
    allMarkerPosition colours w.marker ∈ t.val := by
  rw [w.coordinates_eq]
  exact Finset.mem_insert_self _ _

theorem unique_marker (w u : MarkerWitness colours v t) : w.marker = u.marker := by
  apply allMarkerPosition_injective colours
  have hm := w.marker_in_coordinates
  rw [u.coordinates_eq] at hm
  rcases Finset.mem_insert.mp hm with he | hm
  · exact he
  · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
    exact False.elim (markerPosition_ne_original colours w.marker.2 x hx.symm)

instance subsingleton : Subsingleton (MarkerWitness colours v t) := by
  refine ⟨fun w u => ?_⟩
  have hm := unique_marker w u
  have hp : w.originalPrefix = u.originalPrefix := by
    apply Finset.image_injective (originalHeight_strictMono colours).injective
    have he := congrArg (fun s : Finset ℕ => s.erase (allMarkerPosition colours w.marker))
      (w.coordinates_eq.symm.trans u.coordinates_eq)
    rw [← hm] at he
    have hnotu : allMarkerPosition colours w.marker ∉
        u.originalPrefix.image (originalHeight colours) := by
      rw [hm]
      exact u.marker_not_in_original_image
    simpa only [Finset.erase_insert w.marker_not_in_original_image,
      Finset.erase_insert hnotu] using he
  cases w
  cases u
  cases hm
  cases hp
  rfl

theorem no_original (w : MarkerWitness colours v t) :
    ¬ Nonempty (OriginalWitness colours v t) := by
  rintro ⟨o⟩
  have hm := w.marker_in_coordinates
  rw [← o.image_eq] at hm
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
  exact markerPosition_ne_original colours w.marker.2 x hx.symm

theorem marker_is_minimum (w : MarkerWitness colours v t) {x : ℕ} (hx : x ∈ t.val) :
    allMarkerPosition colours w.marker ≤ x := by
  rw [w.coordinates_eq] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (marker_lt_original_of_le colours (Nat.le_of_lt (w.prefix_gt y hy)) w.marker.2).le

end MarkerWitness

noncomputable def codeValue (c : ∀ v, GenuineColours colours v) (v : ℕ)
    (t : Coordinate (originalHeight colours v)) : ℕ := by
  classical
  exact if ho : Nonempty (OriginalWitness colours v t) then (c v (Classical.choice ho).support).val
  else if hm : Nonempty (MarkerWitness colours v t) then
    let w := Classical.choice hm
    if (c v w.fullSupport).val = w.marker.2.2.val + 1 then colours t.val.card + 1 else 0
  else 0

theorem codeValue_lt (c : ∀ v, GenuineColours colours v) (v : ℕ)
    (t : Coordinate (originalHeight colours v)) :
    codeValue colours c v t < colours t.val.card + 2 := by
  classical
  unfold codeValue
  split_ifs with ho hm
  · let o := Classical.choice ho
    have ht : t.val.card = o.support.val.card := by
      rw [← o.image_eq, Finset.card_image_of_injective _ (originalHeight_strictMono colours).injective]
    have hp := (c v o.support).isLt
    change (c v o.support).val < colours t.val.card + 2
    rw [ht]
    omega
  · dsimp only
    split_ifs <;> omega
  · omega

noncomputable def family (c : ∀ v, GenuineColours colours v) (v : ℕ) : Node (Alphabet colours) 0 where
  height := originalHeight colours v
  table t := ⟨codeValue colours c v t, by simpa only [Nat.zero_add] using codeValue_lt colours c v t⟩

@[simp] theorem family_height (c : ∀ v, GenuineColours colours v) (v : ℕ) :
    (family colours c v).height = originalHeight colours v := rfl

theorem family_injective (c : ∀ v, GenuineColours colours v) :
    Function.Injective (family colours c) := by
  intro u v h
  exact (originalHeight_strictMono colours).injective (congrArg Node.height h)

theorem original_value (c : ∀ v, GenuineColours colours v) {v : ℕ} (s : Coordinate v) :
    ((family colours c v).table (mapOriginal colours s)).val = (c v s).val := by
  classical
  let o : OriginalWitness colours v (mapOriginal colours s) := ⟨s, rfl⟩
  have ho : Nonempty (OriginalWitness colours v (mapOriginal colours s)) := ⟨o⟩
  change codeValue colours c v (mapOriginal colours s) = _
  rw [codeValue, dif_pos ho]
  rw [show Classical.choice ho = o from Subsingleton.elim _ _]

theorem marker_value (c : ∀ v, GenuineColours colours v) {v : ℕ}
    {t : Coordinate (originalHeight colours v)} (w : MarkerWitness colours v t) :
    ((family colours c v).table t).val =
      if (c v w.fullSupport).val = w.marker.2.2.val + 1 then colours t.val.card + 1 else 0 := by
  classical
  have hm : Nonempty (MarkerWitness colours v t) := ⟨w⟩
  change codeValue colours c v t = _
  rw [codeValue, dif_neg w.no_original, dif_pos hm]
  rw [show Classical.choice hm = w from Subsingleton.elim _ _]

theorem codeValue_zero_of_marker_not_minimum (c : ∀ v, GenuineColours colours v) {v : ℕ}
    (t : Coordinate (originalHeight colours v)) (p q : ℕ)
    (hp : p ∈ t.val) (hM : p ∈ markerPositions colours) (hq : q ∈ t.val) (hqp : q < p) :
    codeValue colours c v t = 0 := by
  classical
  have ho : ¬ Nonempty (OriginalWitness colours v t) := by
    rintro ⟨o⟩
    have hp' := hp
    rw [← o.image_eq] at hp'
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp'
    exact hM ⟨x, hx⟩
  have hm : ¬ Nonempty (MarkerWitness colours v t) := by
    rintro ⟨w⟩
    have hp' := hp
    rw [w.coordinates_eq] at hp'
    rcases Finset.mem_insert.mp hp' with he | hp'
    · have hle := w.marker_is_minimum hq
      omega
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp'
      exact hM ⟨x, hx⟩
  simp [codeValue, ho, hm]

end CombinedRamsey.Positive.Marker
