import CombinedRamsey.Positive.MarkerShapes

/-! Classification is derived from the concrete three-case code function.
No shape assumption is added to the marker-family separation proof. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

theorem coordinate_shape_of_nonzero {colours : ℕ → ℕ} {c : ∀ v, GenuineColours colours v}
    {i v n : ℕ} {s : Node (Alphabet colours) i}
    (S : OriginalSliceRecord colours c v s) (hs : originalHeight colours n < s.height)
    (C : Coordinate (originalHeight colours n + 1)) (hTop : originalHeight colours n ∈ C.val)
    (hNZ : (s.table (C.inclusion (by omega))).val ≠ 0) : CoordinateShape colours i n C.val := by
  classical
  let M := mergeCoordinates colours v S.record.slicingCoordinates s.height S.record.bounds
    S.record.height_bound (C.inclusion (by omega))
  have hmax : ∀ x ∈ C.val, x ≤ originalHeight colours n := by
    intro x hx
    have hx' := Finset.mem_range.mp (C.property.2 hx)
    omega
  have hdis := S.local_coordinate_disjoint hs C
  by_cases ho : Nonempty (OriginalWitness colours v M)
  · let o := Classical.choice ho
    have hOrig : ∀ x ∈ C.val, x ∈ originalPositions colours := by
      intro x hx
      have hm : x ∈ M.val := Finset.mem_union_right _ hx
      rw [← o.image_eq] at hm
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hm
      exact ⟨y, hy⟩
    let R := originalPreimage colours C.val
    have hRimage : R.image (originalHeight colours) = C.val := originalPreimage_image colours C.val hOrig
    have hRbound : R ⊆ Finset.range (n + 1) := by
      intro y hy
      have hx : originalHeight colours y ∈ C.val := by
        rw [← hRimage]
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      have hle := (originalHeight_strictMono colours).le_iff_le.mp (hmax _ hx)
      exact Finset.mem_range.mpr (by omega)
    have hRtop : n ∈ R := by
      have hn : originalHeight colours n ∈ R.image (originalHeight colours) := hRimage.symm ▸ hTop
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hn
      exact (originalHeight_strictMono colours).injective he ▸ hy
    exact CoordinateShape.original ⟨R, ⟨n, hRtop⟩, hRbound⟩ hRtop hRimage.symm
  · by_cases hd : Nonempty (MarkerWitness colours v M)
    · let d := Classical.choice hd
      let P := d.originalPrefix \ S.originalPrefix
      have hmC : allMarkerPosition colours d.marker ∈ C.val := by
        have hm := d.marker_in_coordinates
        change allMarkerPosition colours d.marker ∈ S.record.slicingCoordinates ∪ C.val at hm
        rcases Finset.mem_union.mp hm with hm | hm
        · rw [← S.image_eq] at hm
          obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hm
          exact False.elim (markerPosition_ne_original colours d.marker.2 y hy.symm)
        · exact hm
      have hβ : d.marker.1 ≤ n := by
        by_contra hn
        have hl := original_lt_marker_of_lt colours (show n < d.marker.1 by omega) d.marker.2
        have hu := hmax _ hmC
        change originalHeight colours n < allMarkerPosition colours d.marker at hl
        omega
      have hEq : C.val = insert (allMarkerPosition colours d.marker) (P.image (originalHeight colours)) := by
        apply Finset.ext
        intro x
        constructor
        · intro hx
          have hm : x ∈ M.val := Finset.mem_union_right _ hx
          rw [d.coordinates_eq] at hm
          rcases Finset.mem_insert.mp hm with hxM | hxQ
          · exact Finset.mem_insert.mpr (Or.inl hxM)
          · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hxQ
            have hnot : y ∉ S.originalPrefix := by
              intro hyP
              have hxS : x ∈ S.record.slicingCoordinates := by
                rw [← S.image_eq]
                exact Finset.mem_image.mpr ⟨y, hyP, he⟩
              exact Finset.disjoint_left.mp hdis hxS hx
            exact Finset.mem_insert.mpr (Or.inr
              (Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy, hnot⟩, he⟩))
        · intro hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hmC
          · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
            have hm : originalHeight colours y ∈ M.val := by
              rw [d.coordinates_eq]
              exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
                ⟨y, (Finset.mem_sdiff.mp hy).1, rfl⟩)
            change originalHeight colours y ∈ S.record.slicingCoordinates ∪ C.val at hm
            rcases Finset.mem_union.mp hm with hm | hm
            · rw [← S.image_eq] at hm
              obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
              exact False.elim ((Finset.mem_sdiff.mp hy).2
                ((originalHeight_strictMono colours).injective he ▸ hz))
            · exact hm
      have hP : ∀ x ∈ P, x ≤ n := by
        intro x hx
        have hxC : originalHeight colours x ∈ C.val := by
          rw [hEq]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        exact (originalHeight_strictMono colours).le_iff_le.mp (hmax _ hxC)
      have hgt : ∀ x ∈ P, d.marker.1 < x :=
        fun x hx => d.prefix_gt x (Finset.mem_sdiff.mp hx).1
      have hntop : n ∈ P := by
        have hTop' := hTop
        rw [hEq] at hTop'
        rcases Finset.mem_insert.mp hTop' with he | hm
        · exact False.elim (markerPosition_ne_original colours d.marker.2 n he.symm)
        · obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hm
          exact (originalHeight_strictMono colours).injective he ▸ hx
      have houter : S.originalPrefix ⊆ d.originalPrefix := by
        intro y hy
        have hm : originalHeight colours y ∈ M.val := by
          change originalHeight colours y ∈ S.record.slicingCoordinates ∪ C.val
          apply Finset.mem_union_left
          rw [← S.image_eq]
          exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
        rw [d.coordinates_eq] at hm
        rcases Finset.mem_insert.mp hm with he | hm
        · exact False.elim (markerPosition_ne_original colours d.marker.2 y he.symm)
        · obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
          exact (originalHeight_strictMono colours).injective he ▸ hz
      have hprefix : S.originalPrefix ∪ P = d.originalPrefix :=
        Finset.union_sdiff_of_subset houter
      have hdisPrefix : Disjoint S.originalPrefix P := by
        apply Finset.disjoint_left.mpr
        intro y hy hp
        exact (Finset.mem_sdiff.mp hp).2 hy
      have hcard : d.originalPrefix.card = i + P.card := by
        rw [← hprefix, Finset.card_union_of_disjoint hdisPrefix, S.cardinality]
      have hdepth : i + P.card ≤ d.marker.1 := by
        rw [← hcard]
        exact d.depth_bound
      exact CoordinateShape.marker d.marker P hβ hP hgt hntop hdepth hEq
    · have hz : codeValue colours c v M = 0 := by
        simp only [codeValue, dif_neg ho, dif_neg hd]
      have he := S.record.evaluate (C.inclusion (by omega))
      exact False.elim (hNZ (he.trans hz))

end CombinedRamsey.Positive.Marker


