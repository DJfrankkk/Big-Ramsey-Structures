import CombinedRamsey.Positive.MarkerSliceRecords

/-! Nonzero actual slices have a uniquely decoded all-original slicing prefix. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

variable (colours : ℕ → ℕ)

noncomputable def originalPreimage (P : Finset ℕ) : Finset ℕ :=
  P.image (Function.invFun (originalHeight colours))

theorem originalPreimage_image (P : Finset ℕ)
    (hP : ∀ p ∈ P, p ∈ originalPositions colours) :
    (originalPreimage colours P).image (originalHeight colours) = P := by
  classical
  rw [originalPreimage, Finset.image_image]
  calc
    P.image (originalHeight colours ∘ Function.invFun (originalHeight colours)) = P.image id := by
      apply Finset.image_congr
      intro p hp
      exact Function.invFun_eq (hP p hp)
    _ = P := Finset.image_id

structure OriginalSliceRecord (c : ∀ v, GenuineColours colours v) (v : ℕ)
    {i : ℕ} (t : Node (Alphabet colours) i) where
  record : SliceRecord colours c v t
  originalPrefix : Finset ℕ
  image_eq : originalPrefix.image (originalHeight colours) = record.slicingCoordinates

namespace OriginalSliceRecord

variable {colours} {c : ∀ v, GenuineColours colours v} {v i : ℕ} {t : Node (Alphabet colours) i}

noncomputable def of_nonzero (w : SliceRecord colours c v t) (ht : t ≠ Node.zero i t.height) :
    OriginalSliceRecord colours c v t := by
  have hOrig : ∀ p ∈ w.slicingCoordinates, p ∈ originalPositions colours := by
    intro p hp
    by_contra hD
    exact ht (w.zero_of_marker_prefix p hp hD)
  exact ⟨w, originalPreimage colours w.slicingCoordinates,
    originalPreimage_image colours w.slicingCoordinates hOrig⟩

theorem cardinality (w : OriginalSliceRecord colours c v t) : w.originalPrefix.card = i := by
  have hc := congrArg Finset.card w.image_eq
  rw [Finset.card_image_of_injective _ (originalHeight_strictMono colours).injective] at hc
  exact hc.trans w.record.cardinality

theorem prefix_lt (w : OriginalSliceRecord colours c v t) {x : ℕ} (hx : x ∈ w.originalPrefix) : x < v := by
  have hp : originalHeight colours x ∈ w.record.slicingCoordinates := by
    rw [← w.image_eq]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hlt := Finset.mem_range.mp (w.record.bounds hp)
  exact (originalHeight_strictMono colours).lt_iff_lt.mp hlt

theorem prefix_above (w : OriginalSliceRecord colours c v t) {x : ℕ} (hx : x ∈ w.originalPrefix) :
    t.height ≤ originalHeight colours x := by
  apply w.record.above
  rw [← w.image_eq]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem origin_above (w : OriginalSliceRecord colours c v t) {n : ℕ}
    (hn : originalHeight colours n < t.height) : n < v :=
  (originalHeight_strictMono colours).lt_iff_lt.mp (hn.trans_le w.record.height_bound)

theorem prefix_above_original (w : OriginalSliceRecord colours c v t) {n x : ℕ}
    (hn : originalHeight colours n < t.height) (hx : x ∈ w.originalPrefix) : n < x :=
  (originalHeight_strictMono colours).lt_iff_lt.mp (hn.trans_le (w.prefix_above hx))

end OriginalSliceRecord
end CombinedRamsey.Positive.Marker


