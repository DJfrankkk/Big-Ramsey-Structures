import CombinedRamsey.Positive.MarkerSliceRecords
import RelationalRamsey632.Coding.SeparatedClosure

/-! Actual evaluated-slice separation of the constructed marker family. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source RelationalRamsey632.Coding

variable (colours : ℕ → ℕ) (c : ∀ v, GenuineColours colours v)

theorem evaluated_family_slice {v i : ℕ} (coords : Fin i → ℕ)
    (t : Node (Alphabet colours) i) (he : evaluateSlices (family colours c v) i coords = some t) :
    IteratedSlice colours c v i t := by
  induction i with
  | zero =>
    have ht : family colours c v = t := by simpa [evaluateSlices] using he
    exact ht ▸ IteratedSlice.initial
  | succ i ih =>
    cases hp : evaluateSlices (family colours c v) i (fun j => coords j.castSucc) with
    | none => simp [evaluateSlices, hp] at he
    | some u =>
      by_cases hn : coords (Fin.last i) < u.height
      · have ht : u.slice (coords (Fin.last i)) hn = t := by
          simpa [evaluateSlices, hp, hn] using he
        exact ht ▸ IteratedSlice.step (ih _ u hp) _ hn
      · simp [evaluateSlices, hp, hn] at he

theorem evaluated_marker_prefix_zero {v i : ℕ} (coords : Fin i → ℕ)
    (t : Node (Alphabet colours) i) (he : evaluateSlices (family colours c v) i coords = some t)
    (hD : ∃ j, coords j ∈ markerPositions colours) : t = Node.zero i t.height := by
  induction i with
  | zero => obtain ⟨j, _⟩ := hD; exact j.elim0
  | succ i ih =>
    cases hp : evaluateSlices (family colours c v) i (fun j => coords j.castSucc) with
    | none => simp [evaluateSlices, hp] at he
    | some u =>
      by_cases hn : coords (Fin.last i) < u.height
      · have ht : u.slice (coords (Fin.last i)) hn = t := by
          simpa [evaluateSlices, hp, hn] using he
        subst t
        by_cases hprev : ∃ j : Fin i, coords j.castSucc ∈ markerPositions colours
        · have hu := ih _ u hp hprev
          exact (node_slice_congr hu _ hn hn).trans (Node.zero_slice _ _ _ hn)
        · have hlast : coords (Fin.last i) ∈ markerPositions colours := by
            obtain ⟨j, hj⟩ := hD
            have hcases : ∀ j : Fin (i + 1),
                coords j ∈ markerPositions colours → coords (Fin.last i) ∈ markerPositions colours := by
              intro j
              refine Fin.lastCases ?_ (fun k => ?_) j
              · exact id
              · intro hk
                exact False.elim (hprev ⟨k, hk⟩)
            exact hcases j hj
          exact slice_at_marker_zero colours c _ (evaluated_family_slice colours c _ u hp) _ hn hlast
      · simp [evaluateSlices, hp, hn] at he

def familyRange : Set (Node (Alphabet colours) 0) := Set.range (family colours c)

theorem family_generators_original :
    ∀ t ∈ familyRange colours c, t.height ∈ originalPositions colours := by
  rintro t ⟨v, rfl⟩
  exact ⟨v, rfl⟩

theorem family_marker_slices :
    ∀ (s : Node (Alphabet colours) 0) (_ : s ∈ familyRange colours c) (i : ℕ) (coords : Fin i → ℕ)
      (t : Node (Alphabet colours) i), evaluateSlices s i coords = some t →
      (∃ j, coords j ∉ originalPositions colours) → t = Node.zero i t.height := by
  rintro s ⟨v, rfl⟩ i coords t he hD
  exact evaluated_marker_prefix_zero colours c coords t he hD

end CombinedRamsey.Positive.Marker


