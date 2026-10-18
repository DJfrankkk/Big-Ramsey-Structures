import RelationalRamsey632.Coding.ZeroNodes

/-! The exact last zero restriction, including all zero-comparator meets. -/

namespace RelationalRamsey632.Source.Node

variable {A : ℕ → Type} [∀ j, Zero (A j)] {i : ℕ}

noncomputable def zeroBoundary (g : Node A i) : ℕ :=
  meetHeight g (zero i g.height)

theorem zeroBoundary_le (g : Node A i) : zeroBoundary g ≤ g.height :=
  meetHeight_le_left _ _

theorem commonHeight_zero_iff (g : Node A i) (m n : ℕ) :
    CommonHeight g (zero i m) n ↔
      n ≤ m ∧ ∃ h : n ≤ g.height, g.restrict n h = zero i n := by
  constructor
  · rintro ⟨hg, hz, he⟩
    exact ⟨hz, hg, he⟩
  · rintro ⟨hz, hg, he⟩
    exact ⟨hg, hz, he⟩

theorem zero_restriction_height_le_boundary (g : Node A i) (n : ℕ)
    (h : n ≤ g.height) (he : g.restrict n h = zero i n) : n ≤ zeroBoundary g :=
  commonHeight_le_meetHeight ((commonHeight_zero_iff g g.height n).mpr ⟨h, h, he⟩)

theorem zeroBoundary_restriction_zero (g : Node A i) :
    g.restrict (zeroBoundary g) (zeroBoundary_le g) = zero i (zeroBoundary g) :=
  ((commonHeight_zero_iff g g.height (zeroBoundary g)).mp
    (commonHeight_meetHeight g (zero i g.height))).2.choose_spec

theorem zeroBoundary_eq_height_iff (g : Node A i) :
    zeroBoundary g = g.height ↔ g = zero i g.height := by
  constructor
  · intro h
    have he := zeroBoundary_restriction_zero g
    simpa [h] using he
  · intro h
    unfold zeroBoundary
    rw [h]
    have he := congrArg height (zero_meet (A := A) i g.height g.height)
    simpa only [height_meet, zero_height, Nat.min_self] using he

theorem zero_comparator_incomparable (g : Node A i) (hg : g ≠ zero i g.height) :
    ¬ Prefix g (zero i g.height) ∧ ¬ Prefix (zero i g.height) g := by
  constructor
  · intro h
    exact hg (prefix_eq_of_height_eq h rfl)
  · intro h
    exact hg (prefix_eq_of_height_eq h rfl).symm

theorem meetHeight_zero (g : Node A i) (m : ℕ) :
    meetHeight g (zero i m) = min m (zeroBoundary g) := by
  apply Nat.le_antisymm
  · obtain ⟨hm, hn, he⟩ := (commonHeight_zero_iff g m _).mp
      (commonHeight_meetHeight g (zero i m))
    exact Nat.le_min.mpr ⟨hm, zero_restriction_height_le_boundary g _ hn he⟩
  · apply commonHeight_le_meetHeight
    apply (commonHeight_zero_iff g m _).mpr
    refine ⟨Nat.min_le_left _ _, ?_⟩
    have hc := commonHeight_downward (commonHeight_meetHeight g (zero i g.height))
      (Nat.min_le_right m (zeroBoundary g))
    exact ((commonHeight_zero_iff g g.height _).mp hc).2

theorem meet_zero (g : Node A i) (m : ℕ) :
    meet g (zero i m) = zero i (min m (zeroBoundary g)) := by
  have he := ((prefix_zero_iff _).mp (meet_prefix_right g (zero i m))).2
  simpa only [height_meet, meetHeight_zero] using he

theorem zeroBoundary_restrict (g : Node A i) (n : ℕ) (hn : n ≤ g.height) :
    zeroBoundary (g.restrict n hn) = min n (zeroBoundary g) := by
  change meetHeight (g.restrict n hn) ((zero i g.height).restrict n hn) = _
  rw [meetHeight_restrictions]
  simp only [← Nat.min_assoc, Nat.min_self]
  rfl

end RelationalRamsey632.Source.Node
