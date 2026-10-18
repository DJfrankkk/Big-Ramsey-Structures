import RelationalRamsey632.Coding.Blocks
import RelationalRamsey632.Coding.ZeroNodes
import RelationalRamsey632.Digits

/-! The actual all-arity source-node digit family, on finite-set coordinates. -/

namespace RelationalRamsey632.Coding

open Source

variable (b : ℕ → ℕ)

abbrev Alphabet (j : ℕ) := Fin (CodingBounds.alphabetSize b j)

instance alphabetNonzero (j : ℕ) : NeZero (CodingBounds.alphabetSize b j) :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (CodingBounds.alphabet_at_least_two b j))⟩

abbrev OriginalProfile (v : ℕ) := (s : Coordinate v) → Fin (b s.val.card)

def mapOriginal {v : ℕ} (s : Coordinate v) : Coordinate (originalHeight b v) :=
  ⟨s.val.image (originalHeight b), s.property.1.image _, by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr
      ((originalHeight_strictMono b) (Finset.mem_range.mp (s.property.2 hx)))⟩

@[simp] theorem mapOriginal_card {v : ℕ} (s : Coordinate v) :
    (mapOriginal b s).val.card = s.val.card :=
  Finset.card_image_of_injective _ (originalHeight_strictMono b).injective

structure OriginalWitness (v : ℕ) (t : Coordinate (originalHeight b v)) where
  support : Coordinate v
  image_eq : support.val.image (originalHeight b) = t.val

instance originalWitnessSubsingleton (v : ℕ) (t : Coordinate (originalHeight b v)) :
    Subsingleton (OriginalWitness b v t) := by
  refine ⟨fun s u => ?_⟩
  have hs : s.support = u.support := by
    apply Subtype.ext
    exact Finset.image_injective (originalHeight_strictMono b).injective
      (s.image_eq.trans u.image_eq.symm)
  cases s
  cases u
  cases hs
  rfl

def betaSupport {n : ℕ} (β : Beta b n) : Finset ℕ :=
  insert n (β.1.image Fin.val)

theorem betaSupport_nonempty {n : ℕ} (β : Beta b n) : (betaSupport b β).Nonempty :=
  ⟨n, Finset.mem_insert_self _ _⟩

theorem betaSupport_lt {n : ℕ} (β : Beta b n) {x : ℕ} (hx : x ∈ betaSupport b β) : x ≤ n := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.le_of_lt i.isLt

structure DigitWitness (v : ℕ) (t : Coordinate (originalHeight b v)) where
  marker : Sigma (Beta b)
  originalPrefix : Finset ℕ
  marker_lt : marker.1 < v
  prefix_lt : ∀ x ∈ originalPrefix, x < v
  prefix_gt : ∀ x ∈ originalPrefix, marker.1 < x
  coordinates_eq : t.val = insert (allBetaPosition b marker) (originalPrefix.image (originalHeight b))

namespace DigitWitness

variable {b} {v : ℕ} {t : Coordinate (originalHeight b v)}

def fullSupport (w : DigitWitness b v t) : Coordinate v :=
  ⟨w.originalPrefix ∪ betaSupport b w.marker.2, by
    obtain ⟨x, hx⟩ := betaSupport_nonempty b w.marker.2
    exact ⟨x, Finset.mem_union_right _ hx⟩, by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_range.mpr (w.prefix_lt x hx)
    · exact Finset.mem_range.mpr ((betaSupport_lt b w.marker.2 hx).trans_lt w.marker_lt)⟩

theorem marker_not_in_original_image (w : DigitWitness b v t) :
    allBetaPosition b w.marker ∉ w.originalPrefix.image (originalHeight b) := by
  rintro hm
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
  exact betaPosition_ne_original b w.marker.2 x hx.symm

theorem coordinate_card (w : DigitWitness b v t) : t.val.card = w.originalPrefix.card + 1 := by
  rw [w.coordinates_eq, Finset.card_insert_of_notMem w.marker_not_in_original_image]
  rw [Finset.card_image_of_injective _ (originalHeight_strictMono b).injective]

theorem marker_in_coordinates (w : DigitWitness b v t) : allBetaPosition b w.marker ∈ t.val := by
  rw [w.coordinates_eq]
  exact Finset.mem_insert_self _ _

theorem unique_marker (w u : DigitWitness b v t) : w.marker = u.marker := by
  apply allBetaPosition_injective b
  have hm := w.marker_in_coordinates
  rw [u.coordinates_eq] at hm
  rcases Finset.mem_insert.mp hm with he | hm
  · exact he
  · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
    exact False.elim (betaPosition_ne_original b w.marker.2 x hx.symm)

instance subsingleton : Subsingleton (DigitWitness b v t) := by
  refine ⟨fun w u => ?_⟩
  have hm := unique_marker w u
  have hp : w.originalPrefix = u.originalPrefix := by
    apply Finset.image_injective (originalHeight_strictMono b).injective
    have he := congrArg (fun s : Finset ℕ => s.erase (allBetaPosition b w.marker))
      (w.coordinates_eq.symm.trans u.coordinates_eq)
    rw [← hm] at he
    have hnotu : allBetaPosition b w.marker ∉ u.originalPrefix.image (originalHeight b) := by
      rw [hm]
      exact u.marker_not_in_original_image
    simpa only [Finset.erase_insert w.marker_not_in_original_image,
      Finset.erase_insert hnotu] using he
  cases w
  cases u
  cases hm
  cases hp
  rfl

theorem no_original (w : DigitWitness b v t) : ¬ Nonempty (OriginalWitness b v t) := by
  rintro ⟨o⟩
  have hm := w.marker_in_coordinates
  rw [← o.image_eq] at hm
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
  exact betaPosition_ne_original b w.marker.2 x hx.symm

theorem marker_is_minimum (w : DigitWitness b v t) {x : ℕ} (hx : x ∈ t.val) :
    allBetaPosition b w.marker ≤ x := by
  rw [w.coordinates_eq] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (beta_lt_original_of_le b (Nat.le_of_lt (w.prefix_gt y hy)) w.marker.2).le

end DigitWitness

noncomputable def codeValue (c : ∀ v, OriginalProfile b v) (v : ℕ)
    (t : Coordinate (originalHeight b v)) : ℕ := by
  classical
  exact if ho : Nonempty (OriginalWitness b v t) then (c v (Classical.choice ho).support).val
  else if hd : Nonempty (DigitWitness b v t) then
    Digits.digit (CodingBounds.alphabetSize b t.val.card)
      (Classical.choice hd).marker.2.2.val (c v (Classical.choice hd).fullSupport).val
  else 0

theorem codeValue_lt (c : ∀ v, OriginalProfile b v) (v : ℕ)
    (t : Coordinate (originalHeight b v)) :
    codeValue b c v t < CodingBounds.alphabetSize b t.val.card := by
  classical
  unfold codeValue
  split_ifs with ho hd
  · let o := Classical.choice ho
    have hc : t.val.card = o.support.val.card := by
      rw [← o.image_eq, Finset.card_image_of_injective _ (originalHeight_strictMono b).injective]
    have hp : 1 ≤ o.support.val.card := o.support.positive_card
    exact (c v o.support).isLt.trans_le (by
      rw [hc]
      exact CodingBounds.profile_le_alphabet b hp (by omega))
  · exact Digits.digit_lt _ _ _ (Nat.pos_of_ne_zero (NeZero.ne _))
  · exact lt_of_lt_of_le (by decide : 0 < 2) (CodingBounds.alphabet_at_least_two b _)

noncomputable def family (c : ∀ v, OriginalProfile b v) (v : ℕ) : Node (Alphabet b) 0 where
  height := originalHeight b v
  table t := ⟨codeValue b c v t, by simpa only [Nat.zero_add] using codeValue_lt b c v t⟩

@[simp] theorem family_height (c : ∀ v, OriginalProfile b v) (v : ℕ) :
    (family b c v).height = originalHeight b v := rfl

theorem original_value (c : ∀ v, OriginalProfile b v) {v : ℕ} (s : Coordinate v) :
    ((family b c v).table (mapOriginal b s)).val = (c v s).val := by
  classical
  let o : OriginalWitness b v (mapOriginal b s) := ⟨s, rfl⟩
  have ho : Nonempty (OriginalWitness b v (mapOriginal b s)) := ⟨o⟩
  change codeValue b c v (mapOriginal b s) = _
  rw [codeValue, dif_pos ho]
  have he : Classical.choice ho = o := Subsingleton.elim _ _
  rw [he]

theorem digit_value (c : ∀ v, OriginalProfile b v) {v : ℕ}
    {t : Coordinate (originalHeight b v)} (w : DigitWitness b v t) :
    ((family b c v).table t).val =
      Digits.digit (CodingBounds.alphabetSize b t.val.card) w.marker.2.2.val
        (c v w.fullSupport).val := by
  classical
  have hd : Nonempty (DigitWitness b v t) := ⟨w⟩
  change codeValue b c v t = _
  rw [codeValue, dif_neg w.no_original, dif_pos hd]
  rw [show Classical.choice hd = w from Subsingleton.elim _ _]

theorem codeValue_zero_of_digit_not_minimum (c : ∀ v, OriginalProfile b v) {v : ℕ}
    (t : Coordinate (originalHeight b v)) (p q : ℕ)
    (hp : p ∈ t.val) (hD : p ∈ digitPositions b) (hq : q ∈ t.val) (hqp : q < p) :
    codeValue b c v t = 0 := by
  classical
  have ho : ¬ Nonempty (OriginalWitness b v t) := by
    rintro ⟨o⟩
    have hp' := hp
    rw [← o.image_eq] at hp'
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp'
    exact hD ⟨x, hx⟩
  have hd : ¬ Nonempty (DigitWitness b v t) := by
    rintro ⟨w⟩
    have hp' := hp
    rw [w.coordinates_eq] at hp'
    rcases Finset.mem_insert.mp hp' with he | hp'
    · have hle := w.marker_is_minimum hq
      omega
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp'
      exact hD ⟨x, hx⟩
  simp [codeValue, ho, hd]

end RelationalRamsey632.Coding

