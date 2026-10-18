import CombinedRamsey.Positive.MarkerWeakMeets
import CombinedRamsey.Positive.WeakMarkedLevels

/-!
The same literal fixed-alphabet marker embedding works at every finite size.
The all-sort intrinsic closure has at most R(k) retained levels, unconditionally.
-/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source RelationalRamsey632.Coding

variable (colours : ℕ → ℕ) (c : ∀ v, GenuineColours colours v)

noncomputable def imageSet (S : Finset ℕ) : Finset (Node (Alphabet colours) 0) := by
  classical
  exact S.image (family colours c)

def allowedVertices (S : Finset ℕ) : Finset ℕ := S ∪ Finset.range S.card

noncomputable def allowedHeights (S : Finset ℕ) : Finset ℕ :=
  (allowedVertices S).image (originalHeight colours)

theorem imageSet_finite (S : Finset ℕ) : (imageSet colours c S : Set (Node (Alphabet colours) 0)).Finite :=
  Finset.finite_toSet _

theorem imageSet_card_le (S : Finset ℕ) :
    Nat.card (imageSet colours c S : Set (Node (Alphabet colours) 0)) ≤ S.card := by
  classical
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact Finset.card_image_le

theorem allowedHeights_card_le (S : Finset ℕ) : (allowedHeights colours S).card ≤ 2 * S.card := by
  classical
  apply Finset.card_image_le.trans
  have h := Finset.card_union_le S (Finset.range S.card)
  simpa only [allowedVertices, Finset.card_range, two_mul] using h

theorem generator_allowed_height (S : Finset ℕ) :
    ∀ t ∈ (imageSet colours c S : Set (Node (Alphabet colours) 0)),
      t.height ∈ allowedHeights colours S := by
  classical
  intro t ht
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_image.mpr ⟨v, Finset.mem_union_left _ hv, rfl⟩

theorem generator_in_familyRange (S : Finset ℕ) :
    (imageSet colours c S : Set (Node (Alphabet colours) 0)) ⊆ familyRange colours c := by
  classical
  intro t ht
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨v, rfl⟩

theorem library_depth_lt_card_above_low (S : Finset ℕ) {i n : ℕ}
    {s : Node (Alphabet colours) i}
    (hs : s ∈ sliceLibrary (Alphabet colours) (imageSet colours c S : Set (Node (Alphabet colours) 0))
      (allowedHeights colours S) i)
    (habove : originalHeight colours n < s.height) (hn : S.card ≤ n) : i < S.card := by
  classical
  obtain ⟨origin, horigin, coords, hcoords, he⟩ := hs
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp horigin
  let HS := S.image (originalHeight colours)
  have hcoordsS : ∀ j, coords j ∈ HS := by
    intro j
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (hcoords j)
    have hab := (evaluateSlices_invariant (family colours c v) i coords s he).2.1 j
    have hna : n < a := (originalHeight_strictMono colours).lt_iff_lt.mp (by omega)
    have haS : a ∈ S := by
      rcases Finset.mem_union.mp ha with haS | haSmall
      · exact haS
      · have hsmall := Finset.mem_range.mp haSmall
        omega
    exact Finset.mem_image.mpr ⟨a, haS, hea⟩
  have hsHS : s ∈ sliceLibrary (Alphabet colours)
      (imageSet colours c S : Set (Node (Alphabet colours) 0)) HS i :=
    ⟨family colours c v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, coords, hcoordsS, he⟩
  have hheight : ∀ t ∈ (imageSet colours c S : Set (Node (Alphabet colours) 0)), t.height ∈ HS := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hdepth := sliceLibrary_depth_bound (Alphabet colours)
    (imageSet colours c S : Set (Node (Alphabet colours) 0)) HS hheight hsHS
  have hcard : HS.card ≤ S.card := Finset.card_image_le
  omega

theorem library_proper_original_trap (S : Finset ℕ) (N : ℕ) {i : ℕ}
    {s t : Node (Alphabet colours) i}
    (hs : s ∈ CombinedRamsey.Positive.augmentedFamily
      (sliceLibrary (Alphabet colours) (imageSet colours c S : Set (Node (Alphabet colours) 0))
        (allowedHeights colours S)) N i)
    (ht : t ∈ CombinedRamsey.Positive.augmentedFamily
      (sliceLibrary (Alphabet colours) (imageSet colours c S : Set (Node (Alphabet colours) 0))
        (allowedHeights colours S)) N i)
    (hst : ¬ Node.Prefix s t) (hts : ¬ Node.Prefix t s)
    (hO : s.meetHeight t ∈ originalPositions colours) :
    s.meetHeight t ∈ allowedHeights colours S := by
  classical
  obtain ⟨n, hn⟩ := hO
  have hproper := Node.meetHeight_lt_of_incomparable hst hts
  have haboves : originalHeight colours n < s.height := by omega
  have habovet : originalHeight colours n < t.height := by omega
  have hcands : SliceOrZero (familyRange colours c) i s := by
    rcases hs with hs | hs
    · exact Or.inl (library_descendant (generator_in_familyRange colours c S) hs)
    · change s = Node.zero i N at hs
      exact Or.inr (by rw [hs]; rfl)
  have hcandt : SliceOrZero (familyRange colours c) i t := by
    rcases ht with ht | ht
    · exact Or.inl (library_descendant (generator_in_familyRange colours c S) ht)
    · change t = Node.zero i N at ht
      exact Or.inr (by rw [ht]; rfl)
  have hni := family_weak_proper_meet colours c i s t hcands hcandt hst hts n hn.symm
  have hnk : n < S.card := by
    by_contra hk
    have hk' : S.card ≤ n := by omega
    rcases hs with hs | hs
    · have hi := library_depth_lt_card_above_low colours c S hs haboves hk'
      omega
    · rcases ht with ht | ht
      · have hi := library_depth_lt_card_above_low colours c S ht habovet hk'
        omega
      · change s = Node.zero i N at hs
        change t = Node.zero i N at ht
        exact hst (by simpa only [hs, ht] using Node.prefix_refl (Node.zero (A := Alphabet colours) i N))
  rw [← hn]
  exact Finset.mem_image.mpr ⟨n, Finset.mem_union_right _ (Finset.mem_range.mpr hnk), rfl⟩

theorem allowedVertices_le_max (S : Finset ℕ) (hne : S.Nonempty) :
    ∀ a ∈ allowedVertices S, a ≤ S.max' hne := by
  have hcard : S.card ≤ S.max' hne + 1 := by
    calc
      S.card ≤ (Finset.range (S.max' hne + 1)).card := Finset.card_le_card (by
        intro x hx
        exact Finset.mem_range.mpr (by have := Finset.le_max' S x hx; omega))
      _ = S.max' hne + 1 := Finset.card_range _
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · exact Finset.le_max' S a ha
  · have := Finset.mem_range.mp ha
    omega

/-- Unconditional new fixed-alphabet closure theorem, simultaneously for every finite S. -/
theorem uniform_closure_level_bound (S : Finset ℕ) (hne : S.Nonempty) :
    Nat.card (closureLevels (Alphabet colours)
      (imageSet colours c S : Set (Node (Alphabet colours) 0))) ≤
      CombinedRamsey.Positive.originalEnvelopeBound S.card := by
  classical
  let X : Set (Node (Alphabet colours) 0) := imageSet colours c S
  let H := allowedHeights colours S
  let F := sliceLibrary (Alphabet colours) X H
  let N := originalHeight colours (S.max' hne)
  have hXfin := imageSet_finite colours c S
  have hP := (CombinedRamsey.Positive.all_sort_sliceLibrary_finite_card (Alphabet colours) X H hXfin).1
  letI : Finite (CombinedRamsey.Positive.FamilyIndex F) := hP
  have hHle : ∀ n ∈ H, n ≤ N := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact (originalHeight_strictMono colours).monotone (allowedVertices_le_max S hne a ha)
  have hN : N ∈ H := Finset.mem_image.mpr
    ⟨S.max' hne, Finset.mem_union_left _ (Finset.max'_mem S hne), rfl⟩
  have hheight : ∀ i s, s ∈ F i → s.height ∈ H := by
    intro i s hs
    exact sliceLibrary_height (Alphabet colours) X H (generator_allowed_height colours c S) hs
  have hFle : ∀ i s, s ∈ F i → s.height ≤ N := fun i s hs => hHle _ (hheight i s hs)
  have hmfin := (CombinedRamsey.Positive.weakMarkedSet_finite_card (F := F) (N := N) (H := H)).1
  let L := hmfin.toFinset
  have hLmem (n : ℕ) : n ∈ L ↔ n ∈ CombinedRamsey.Positive.weakMarkedSet F N H :=
    hmfin.mem_toFinset
  have hsub : closureLevels (Alphabet colours) X ⊆ (L : Set ℕ) := by
    apply CombinedRamsey.Positive.intrinsic_levels_subset_weakContainer
      (H := H) (O := originalPositions colours) (F := F) (N := N)
    · intro s hs
      exact sliceLibrary_generator (Alphabet colours) X H hs
    · intro s hs
      exact (hLmem _).mpr (CombinedRamsey.Positive.weakMarkedSet_contains_original
        (generator_allowed_height colours c S s hs))
    · intro n hn
      exact CombinedRamsey.Positive.weakMarkedSet_le hHle hFle n ((hLmem n).mp hn)
    · intro n hn hO
      exact CombinedRamsey.Positive.weakMarkedSet_original_trap hN hheight
        (fun i s t hs ht hst hts hO => library_proper_original_trap colours c S N hs ht hst hts hO)
        n ((hLmem n).mp hn) hO
    · intro i s t hs ht
      exact (hLmem _).mpr (CombinedRamsey.Positive.weakMarkedSet_contains_meet hN hs ht)
    · intro i s hs n hn hlt
      exact sliceLibrary_step (Alphabet colours) X H hs n hn hlt
    · intro i s hs n hlt hM
      obtain ⟨origin, horigin, coords, _, he⟩ := hs
      have he' : evaluateSlices origin (i + 1) (Fin.lastCases n coords) = some (s.slice n hlt) := by
        simp [evaluateSlices, he, hlt]
      exact family_marker_slices colours c origin (generator_in_familyRange colours c S horigin)
        (i + 1) (Fin.lastCases n coords) (s.slice n hlt) he' ⟨Fin.last i, by simpa using hM⟩
  apply CombinedRamsey.Positive.weakContainer_level_card_bound hsub
  have hcard := (CombinedRamsey.Positive.weakMarkedSet_finite_card (F := F) (N := N) (H := H)).2
  have hLcard : L.card = Nat.card (CombinedRamsey.Positive.weakMarkedSet F N H) :=
    (Nat.card_eq_card_finite_toFinset hmfin).symm
  rw [hLcard]
  apply hcard.trans
  exact CombinedRamsey.Positive.originalEnvelopeBound_count (allowedHeights_card_le colours S)
    (CombinedRamsey.Positive.all_sort_sliceLibrary_four_power (Alphabet colours) X H hXfin
      (imageSet_card_le colours c S) (allowedHeights_card_le colours S))

end CombinedRamsey.Positive.Marker
