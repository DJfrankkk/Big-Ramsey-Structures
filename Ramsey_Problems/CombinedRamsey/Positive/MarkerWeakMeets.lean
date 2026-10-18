import CombinedRamsey.Positive.MarkerShapes
import CombinedRamsey.Positive.MarkerFamilySlices
import CombinedRamsey.Positive.MarkerShapeClassification
import RelationalRamsey632.Source.MeetDisagreement

/-! The maximal-meet contradiction from actual recovered coordinate shapes. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source RelationalRamsey632.Coding

variable (colours : ℕ → ℕ) (c : ∀ v, GenuineColours colours v)

def FamilyShapeProperty : Prop :=
  ∀ {i v n : ℕ} {s : Node (Alphabet colours) i} (S : OriginalSliceRecord colours c v s)
    (hs : originalHeight colours n < s.height) (C : Coordinate (originalHeight colours n + 1)),
    originalHeight colours n ∈ C.val →
      (s.table (C.inclusion (by omega))).val ≠ 0 → CoordinateShape colours i n C.val

theorem zero_table_value {i : ℕ} {s : Node (Alphabet colours) i}
    (hs : s = Node.zero i s.height) (C : Coordinate s.height) : (s.table C).val = 0 := by
  cases s with
  | mk n table =>
    have he := Node.mk_injective n hs
    exact congrArg Fin.val (congrFun he C)

theorem commonHeight_swap {i : ℕ} {s t : Node (Alphabet colours) i} {n : ℕ}
    (hc : Node.CommonHeight s t n) : Node.CommonHeight t s n := by
  obtain ⟨hs, ht, he⟩ := hc
  exact ⟨ht, hs, he.symm⟩

theorem commonHeight_right_congr {i : ℕ} {s t u : Node (Alphabet colours) i} {n : ℕ}
    (he : t = u) (hc : Node.CommonHeight s t n) : Node.CommonHeight s u n := by
  cases he
  exact hc

theorem candidate_nonzero_record {i : ℕ} {s : Node (Alphabet colours) i}
    (hcand : SliceOrZero (familyRange colours c) i s) (hs : s ≠ Node.zero i s.height) :
    ∃ v, Nonempty (OriginalSliceRecord colours c v s) := by
  rcases hcand with hdesc | hzero
  · obtain ⟨origin, ⟨v, rfl⟩, coords, he⟩ := hdesc
    obtain ⟨w⟩ := iterated_slice_record colours c v (evaluated_family_slice colours c coords s he)
    exact ⟨v, ⟨OriginalSliceRecord.of_nonzero w hs⟩⟩
  · exact False.elim (hs hzero)

theorem shape_coordinate_agreement
    (hshape : FamilyShapeProperty colours c) {i n : ℕ} {s t : Node (Alphabet colours) i}
    (hscand : SliceOrZero (familyRange colours c) i s) (htcand : SliceOrZero (familyRange colours c) i t)
    (hs : originalHeight colours n < s.height) (ht : originalHeight colours n < t.height)
    (hi : i ≤ n) (hcommon : Node.CommonHeight s t (originalHeight colours n))
    (C : Coordinate (originalHeight colours n + 1)) (hTop : originalHeight colours n ∈ C.val)
    (hNZ : (s.table (C.inclusion (by omega))).val ≠ 0) :
    (s.table (C.inclusion (by omega))).val = (t.table (C.inclusion (by omega))).val := by
  have hsnz : s ≠ Node.zero i s.height := by
    intro he
    exact hNZ (zero_table_value colours he _)
  obtain ⟨v, ⟨S⟩⟩ := candidate_nonzero_record colours c hscand hsnz
  have hcshape := hshape S hs C hTop hNZ
  by_cases htzero : t = Node.zero i t.height
  · have hc0 := commonHeight_right_congr colours htzero hcommon
    have hz := coordinate_shape_zero colours S hs ht hi hc0 C hcshape
    exact False.elim (hNZ hz)
  · obtain ⟨w, ⟨T⟩⟩ := candidate_nonzero_record colours c htcand htzero
    exact coordinate_shape_agreement colours S T hs ht hi hcommon C hcshape

theorem family_weak_proper_meet_of_shapes
    (hshape : FamilyShapeProperty colours c) :
    ∀ (i : ℕ) (s t : Node (Alphabet colours) i),
      SliceOrZero (familyRange colours c) i s → SliceOrZero (familyRange colours c) i t →
      ¬ Node.Prefix s t → ¬ Node.Prefix t s →
      ∀ n, s.meetHeight t = originalHeight colours n → n < i := by
  intro i s t hscand htcand hst hts n hn
  by_contra hni
  have hi : i ≤ n := by omega
  have hproper := Node.meetHeight_lt_of_incomparable hst hts
  have hs : originalHeight colours n < s.height := by omega
  have ht : originalHeight colours n < t.height := by omega
  have hc : Node.CommonHeight s t (originalHeight colours n) := hn.symm ▸ Node.commonHeight_meetHeight s t
  have hraw : ∃ C : Coordinate (s.meetHeight t + 1), s.meetHeight t ∈ C.val ∧
      (s.table (C.inclusion (by omega))).val ≠ (t.table (C.inclusion (by omega))).val := by
    obtain ⟨C, hTop, hneq⟩ := Node.meet_disagreement s t hst hts
    refine ⟨C, hTop, ?_⟩
    intro he
    exact hneq (Fin.ext he)
  have hdis : ∃ C : Coordinate (originalHeight colours n + 1), originalHeight colours n ∈ C.val ∧
      (s.table (C.inclusion (by omega))).val ≠ (t.table (C.inclusion (by omega))).val := by
    obtain ⟨C, hTop, hNe⟩ := hraw
    let C' : Coordinate (originalHeight colours n + 1) :=
      ⟨C.val, C.property.1, by
        intro x hx
        have hx' := C.property.2 hx
        simpa only [← hn] using hx'⟩
    refine ⟨C', by simpa only [← hn] using hTop, ?_⟩
    have hcs : C.inclusion (by omega : s.meetHeight t + 1 ≤ s.height) =
        C'.inclusion (by omega : originalHeight colours n + 1 ≤ s.height) := Subtype.ext rfl
    have hct : C.inclusion (by omega : s.meetHeight t + 1 ≤ t.height) =
        C'.inclusion (by omega : originalHeight colours n + 1 ≤ t.height) := Subtype.ext rfl
    rw [hcs, hct] at hNe
    exact hNe
  obtain ⟨C, hTop, hNe⟩ := hdis
  by_cases hsz : (s.table (C.inclusion (by omega))).val = 0
  · have htnz : (t.table (C.inclusion (by omega))).val ≠ 0 := by
      intro htz
      exact hNe (hsz.trans htz.symm)
    have he := shape_coordinate_agreement colours c hshape htcand hscand ht hs
      hi (commonHeight_swap colours hc) C hTop htnz
    exact hNe he.symm
  · exact hNe (shape_coordinate_agreement colours c hshape hscand htcand hs ht hi hc C hTop hsz)

theorem family_weak_proper_meet :
    ∀ (i : ℕ) (s t : Node (Alphabet colours) i),
      SliceOrZero (familyRange colours c) i s → SliceOrZero (familyRange colours c) i t →
      ¬ Node.Prefix s t → ¬ Node.Prefix t s →
      ∀ n, s.meetHeight t = originalHeight colours n → n < i :=
  family_weak_proper_meet_of_shapes colours c (fun S hs C hTop hNZ =>
    coordinate_shape_of_nonzero S hs C hTop hNZ)

end CombinedRamsey.Positive.Marker

