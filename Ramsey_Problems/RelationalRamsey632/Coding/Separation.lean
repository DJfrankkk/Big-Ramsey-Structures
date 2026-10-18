import RelationalRamsey632.Coding.SliceLibrary
import RelationalRamsey632.Coding.ZeroMeets

/-! The complete all-depth separation hypothesis used in the closure bound. -/

namespace RelationalRamsey632.Coding

open Source

variable {A : ℕ → Type} [∀ j, Zero (A j)]

def SliceDescendant (R : Set (Node A 0)) (i : ℕ) (t : Node A i) : Prop :=
  ∃ s ∈ R, ∃ coords : Fin i → ℕ, evaluateSlices s i coords = some t

def SliceOrZero (R : Set (Node A 0)) (i : ℕ) (t : Node A i) : Prop :=
  SliceDescendant R i t ∨ t = Node.zero i t.height

structure SeparatedAtAllDepths (R : Set (Node A 0)) (O : Set ℕ) : Prop where
  generator_heights : ∀ s ∈ R, s.height ∈ O
  digit_slice_zero : ∀ (s : Node A 0) (_ : s ∈ R) (i : ℕ) (coords : Fin i → ℕ)
    (t : Node A i), evaluateSlices s i coords = some t →
      (∃ j, coords j ∉ O) → t = Node.zero i t.height
  proper_meet : ∀ (i : ℕ) (s t : Node A i), SliceOrZero R i s → SliceOrZero R i t →
    ¬ Node.Prefix s t → ¬ Node.Prefix t s → Node.meetHeight s t ∉ O

omit [∀ j, Zero (A j)] in
theorem library_descendant {R X : Set (Node A 0)} (hXR : X ⊆ R)
    {H : Finset ℕ} {i : ℕ} {t : Node A i} (ht : t ∈ sliceLibrary A X H i) :
    SliceDescendant R i t := by
  obtain ⟨s, hs, coords, _, he⟩ := ht
  exact ⟨s, hXR hs, coords, he⟩

theorem library_zeroBoundary_not_original {R X : Set (Node A 0)} {O : Set ℕ}
    (hsep : SeparatedAtAllDepths R O) (hXR : X ⊆ R)
    {H : Finset ℕ} {i : ℕ} {t : Node A i} (ht : t ∈ sliceLibrary A X H i)
    (hnz : t ≠ Node.zero i t.height) : t.zeroBoundary ∉ O := by
  have hc := Node.zero_comparator_incomparable t hnz
  exact hsep.proper_meet i t (Node.zero i t.height)
    (Or.inl (library_descendant hXR ht)) (Or.inr rfl) hc.1 hc.2

end RelationalRamsey632.Coding
