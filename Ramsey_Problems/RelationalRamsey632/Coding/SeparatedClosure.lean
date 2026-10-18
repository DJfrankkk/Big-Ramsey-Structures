import RelationalRamsey632.Coding.MarkedLevels

/-!
The least intrinsic closure is contained in the finite marked-level envelope.
Zeros in this auxiliary envelope are not adjoined to the intrinsic closure.
-/

namespace RelationalRamsey632.Coding

open Source

variable {A : ℕ → Type} [∀ j, Zero (A j)]

def possibleNodes (X : Set (Node A 0)) (H : Finset ℕ) (m i : ℕ) : Set (Node A i) :=
  {t | t.height ∈ markedLevels X H m ∧
    (t = Node.zero i t.height ∨ ∃ g ∈ sliceLibrary A X H i,
      ∃ h : t.height ≤ g.height, t = g.restrict t.height h)}

theorem possible_zero {X : Set (Node A 0)} {H : Finset ℕ} {m i n : ℕ}
    (hn : n ∈ markedLevels X H m) : Node.zero (A := A) i n ∈ possibleNodes X H m i :=
  ⟨hn, Or.inl rfl⟩

theorem possible_restriction {X : Set (Node A 0)} {H : Finset ℕ} {m i n : ℕ}
    {g : Node A i} (hg : g ∈ sliceLibrary A X H i)
    (hn : n ∈ markedLevels X H m) (h : n ≤ g.height) :
    g.restrict n h ∈ possibleNodes X H m i := ⟨hn, Or.inr ⟨g, hg, h, rfl⟩⟩

theorem min_mem {S : Set ℕ} {n m : ℕ} (hn : n ∈ S) (hm : m ∈ S) : min n m ∈ S := by
  by_cases h : n ≤ m
  · simpa [Nat.min_eq_left h] using hn
  · simpa [Nat.min_eq_right (Nat.le_of_not_ge h)] using hm

omit [∀ j, Zero (A j)] in
theorem node_slice_restriction {i : ℕ} (g : Node A i) (n h : ℕ)
    (hn : n ≤ g.height) (hh : h < n) :
    (g.restrict n hn).slice h hh = g.slice h (hh.trans_le hn) := by
  cases g
  rfl

omit [∀ j, Zero (A j)] in
theorem node_restrict_congr {i : ℕ} {s t : Node A i} (he : s = t) (n : ℕ)
    (hs : n ≤ s.height) (ht : n ≤ t.height) : s.restrict n hs = t.restrict n ht := by
  cases he
  rfl

omit [∀ j, Zero (A j)] in
theorem node_slice_congr {i : ℕ} {s t : Node A i} (he : s = t) (n : ℕ)
    (hs : n < s.height) (ht : n < t.height) : s.slice n hs = t.slice n ht := by
  cases he
  rfl

theorem library_digit_slice_zero {R X : Set (Node A 0)} {O : Set ℕ} {H : Finset ℕ}
    (hsep : SeparatedAtAllDepths R O) (hXR : X ⊆ R)
    {i : ℕ} {g : Node A i} (hg : g ∈ sliceLibrary A X H i)
    (n : ℕ) (hn : n < g.height) (hD : n ∉ O) : g.slice n hn = Node.zero (i + 1) n := by
  obtain ⟨s, hs, coords, _, he⟩ := hg
  have he' : evaluateSlices s (i + 1) (Fin.lastCases n coords) = some (g.slice n hn) := by
    simp [evaluateSlices, he, hn]
  exact hsep.digit_slice_zero s (hXR hs) (i + 1) (Fin.lastCases n coords)
    (g.slice n hn) he' ⟨Fin.last i, by simpa using hD⟩

theorem possibleNodes_closed {R X : Set (Node A 0)} {O : Set ℕ} {H : Finset ℕ} {m : ℕ}
    (hsep : SeparatedAtAllDepths R O) (hXR : X ⊆ R)
    (hheights : ∀ s ∈ X, s.height ∈ H) (hH : H.card ≤ m) :
    Closed A (possibleNodes X H m) (markedLevels X H m) := by
  have depth : ∀ i (g : Node A i), g ∈ sliceLibrary A X H i → i < m := by
    intro i g hg
    have hi := sliceLibrary_depth_bound A X H hheights hg
    omega
  refine ⟨fun _ _ ht => ht.1, ?_, ?_, ?_⟩
  · intro i s t hs ht
    obtain ⟨hsH, hs0 | ⟨g, hg, hgs, hgsEq⟩⟩ := hs
    · obtain ⟨htH, ht0 | ⟨g, hg, hgt, hgtEq⟩⟩ := ht
      · rw [hs0, ht0, Node.zero_meet]
        exact possible_zero (min_mem hsH htH)
      · rw [hs0, hgtEq, Node.meet_comm, Node.meet_zero, Node.zeroBoundary_restrict]
        exact possible_zero (min_mem hsH
          (min_mem htH (library_zeroBoundary_mem (depth i g hg) hg)))
    · obtain ⟨htH, ht0 | ⟨g', hg', hgt, hgtEq⟩⟩ := ht
      · rw [hgsEq, ht0, Node.meet_zero, Node.zeroBoundary_restrict]
        exact possible_zero (min_mem htH
          (min_mem hsH (library_zeroBoundary_mem (depth i g hg) hg)))
      · rw [hgsEq, hgtEq, Node.meet_restrictions]
        exact possible_restriction hg
          (min_mem hsH (min_mem htH
            (library_meetHeight_mem (depth i g hg) hheights hg hg')))
          ((Nat.min_le_left _ _).trans hgs)
  · intro i t n ht hn hnt
    obtain ⟨_, ht0 | ⟨g, hg, hgt, hgtEq⟩⟩ := ht
    · rw [node_restrict_congr ht0 n hnt hnt, Node.zero_restrict]
      exact possible_zero hn
    · rw [node_restrict_congr hgtEq n hnt hnt, Node.restrict_restrict]
      exact possible_restriction hg hn (hnt.trans hgt)
  · intro i t n ht hn hnt
    obtain ⟨_, ht0 | ⟨g, hg, hgt, hgtEq⟩⟩ := ht
    · rw [node_slice_congr ht0 n hnt hnt, Node.zero_slice]
      exact possible_zero hn
    · rw [node_slice_congr hgtEq n hnt hnt, node_slice_restriction]
      by_cases hO : n ∈ O
      · have hnH := marked_originals hsep hXR hheights n hn hO
        have hg' := sliceLibrary_step A X H hg n hnH (hnt.trans_le hgt)
        have he : g.slice n (hnt.trans_le hgt) =
            (g.slice n (hnt.trans_le hgt)).restrict n le_rfl :=
          (Node.restrict_refl _).symm
        rw [he]
        exact possible_restriction hg' hn le_rfl
      · rw [library_digit_slice_zero hsep hXR hg n (hnt.trans_le hgt) hO]
        exact possible_zero hn

theorem intrinsic_levels_subset_marked {R X : Set (Node A 0)} {O : Set ℕ} {H : Finset ℕ} {m : ℕ}
    (hsep : SeparatedAtAllDepths R O) (hXR : X ⊆ R)
    (hheights : ∀ s ∈ X, s.height ∈ H) (hH : H.card ≤ m) :
    closureLevels A X ⊆ markedLevels X H m := by
  apply (generatedClosure_least A X (possibleNodes X H m) (markedLevels X H m)
    (possibleNodes_closed hsep hXR hheights hH) ?_).2
  intro s hs
  refine ⟨original_mem_markedLevels (hheights s hs), Or.inr ?_⟩
  exact ⟨s, sliceLibrary_generator A X H hs, le_rfl, (Node.restrict_refl s).symm⟩

theorem separated_closure_level_bound {R X : Set (Node A 0)} {O : Set ℕ}
    (hsep : SeparatedAtAllDepths R O) (hXR : X ⊆ R) (hX : X.Finite) :
    Nat.card (closureLevels A X) ≤ levelBound (Nat.card X) := by
  let H := generatorHeights A X hX
  have hheights : ∀ s ∈ X, s.height ∈ H := fun _ hs => generatorHeights_contains A X hX hs
  have hH : H.card ≤ Nat.card X := generatorHeights_card A X hX
  have hsub := intrinsic_levels_subset_marked hsep hXR hheights hH
  have hm := markedLevels_finite_card hX hH
  haveI : Finite (markedLevels X H (Nat.card X)) := hm.1.to_subtype
  let f : closureLevels A X → markedLevels X H (Nat.card X) := fun n => ⟨n.val, hsub n.property⟩
  have hf : Function.Injective f := fun n k h =>
    Subtype.ext (congrArg (fun u : markedLevels X H (Nat.card X) => u.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans hm.2

end RelationalRamsey632.Coding
