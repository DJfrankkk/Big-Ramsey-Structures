import RelationalRamsey632.Source.Meets

/-! Actual all-zero source nodes and their behavior under the closure operations. -/

namespace RelationalRamsey632.Source

variable {A : ℕ → Type} [∀ j, Zero (A j)]

theorem cast_zero {m n : ℕ} (h : m = n) : cast (congrArg A h) (0 : A m) = 0 := by
  cases h
  rfl

namespace Node

def zero (i n : ℕ) : Node A i := ⟨n, fun _ => 0⟩

@[simp] theorem zero_height (i n : ℕ) : (zero (A := A) i n).height = n := rfl

@[simp] theorem zero_restrict (i n m : ℕ) (h : m ≤ n) :
    (zero (A := A) i n).restrict m h = zero i m := rfl

@[simp] theorem zero_slice (i n m : ℕ) (h : m < n) :
    (zero (A := A) i n).slice m h = zero (i + 1) m := by
  apply congrArg (Node.mk m)
  funext s
  have hc : i + (Level.sliceCoordinate h s).val.card = i + 1 + s.val.card := by
    rw [Level.sliceCoordinate_card]
    omega
  exact cast_zero hc

@[simp] theorem zero_singleton (i n m : ℕ) (h : m < n) :
    (zero (A := A) i n).singleton m h = 0 := by
  simp [singleton, Level.singleton, zero]
  rfl

@[simp] theorem root_zero (i : ℕ) : root (A := A) i = zero i 0 :=
  (height_zero_unique (zero i 0) rfl).symm

theorem prefix_zero_iff {i n : ℕ} (t : Node A i) :
    Prefix t (zero i n) ↔ t.height ≤ n ∧ t = zero i t.height := by
  constructor
  · rintro ⟨h, he⟩
    exact ⟨h, he.symm⟩
  · rintro ⟨h, he⟩
    exact ⟨h, by simpa using he.symm⟩

@[simp] theorem zero_meet (i n m : ℕ) :
    meet (zero (A := A) i n) (zero i m) = zero i (min n m) := by
  have hleft : Prefix (zero (A := A) i (min n m)) (zero i n) :=
    ⟨Nat.min_le_left _ _, rfl⟩
  have hright : Prefix (zero (A := A) i (min n m)) (zero i m) :=
    ⟨Nat.min_le_right _ _, rfl⟩
  apply prefix_antisymm
  · have hm := meet_prefix_left (zero (A := A) i n) (zero i m)
    have he := (prefix_zero_iff _).mp hm
    have hh : (meet (zero (A := A) i n) (zero i m)).height ≤ min n m :=
      Nat.le_min.mpr ⟨meetHeight_le_left _ _, meetHeight_le_right _ _⟩
    exact (prefix_zero_iff _).mpr ⟨hh, he.2⟩
  · exact common_prefix_prefix_meet hleft hright

omit [∀ j, Zero (A j)] in
theorem commonHeight_restrictions_iff {i : ℕ} (s t : Node A i)
    (a b n : ℕ) (ha : a ≤ s.height) (hb : b ≤ t.height) :
    CommonHeight (s.restrict a ha) (t.restrict b hb) n ↔
      n ≤ a ∧ n ≤ b ∧ CommonHeight s t n := by
  constructor
  · rintro ⟨hna, hnb, he⟩
    refine ⟨hna, hnb, hna.trans ha, hnb.trans hb, ?_⟩
    simpa only [restrict_restrict] using he
  · rintro ⟨hna, hnb, hs, ht, he⟩
    refine ⟨hna, hnb, ?_⟩
    simpa only [restrict_restrict] using he

omit [∀ j, Zero (A j)] in
theorem meetHeight_restrictions {i : ℕ} (s t : Node A i)
    (a b : ℕ) (ha : a ≤ s.height) (hb : b ≤ t.height) :
    meetHeight (s.restrict a ha) (t.restrict b hb) = min a (min b (meetHeight s t)) := by
  apply Nat.le_antisymm
  · have h := (commonHeight_restrictions_iff s t a b _ ha hb).mp
      (commonHeight_meetHeight (s.restrict a ha) (t.restrict b hb))
    exact Nat.le_min.mpr ⟨h.1,
      Nat.le_min.mpr ⟨h.2.1, commonHeight_le_meetHeight h.2.2⟩⟩
  · apply commonHeight_le_meetHeight
    apply (commonHeight_restrictions_iff s t a b _ ha hb).mpr
    refine ⟨Nat.min_le_left _ _, (Nat.min_le_right _ _).trans (Nat.min_le_left _ _), ?_⟩
    exact commonHeight_downward (commonHeight_meetHeight s t)
      ((Nat.min_le_right _ _).trans (Nat.min_le_right _ _))

omit [∀ j, Zero (A j)] in
theorem meet_restrictions {i : ℕ} (s t : Node A i)
    (a b : ℕ) (ha : a ≤ s.height) (hb : b ≤ t.height) :
    meet (s.restrict a ha) (t.restrict b hb) =
      s.restrict (min a (min b (meetHeight s t)))
        ((Nat.min_le_left _ _).trans ha) := by
  simp only [meet, meetHeight_restrictions, restrict_restrict]

end Node
end RelationalRamsey632.Source
