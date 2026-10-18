import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Lean.Elab.Tactic.Omega

/-!
# The actual arbitrary-depth source nodes

A coordinate is a nonempty finite set of natural numbers below the height.
Listing it in decreasing order recovers exactly the decreasing-sequence
coordinates in the paper. The alphabet index is the sort plus its cardinality.
Thus these definitions retain every arity, with no depth truncation.
-/

namespace RelationalRamsey632.Source

abbrev Coordinate (n : ℕ) :=
  {s : Finset ℕ // s.Nonempty ∧ s ⊆ Finset.range n}

def Coordinate.inclusion {m n : ℕ} (h : m ≤ n) (s : Coordinate m) :
    Coordinate n :=
  ⟨s.val, s.property.1, s.property.2.trans (Finset.range_mono h)⟩

@[simp] theorem Coordinate.inclusion_val {m n : ℕ} (h : m ≤ n)
    (s : Coordinate m) : (s.inclusion h).val = s.val := rfl

theorem Coordinate.positive_card {n : ℕ} (s : Coordinate n) : 0 < s.val.card :=
  Finset.card_pos.mpr s.property.1

noncomputable instance coordinateFintype (n : ℕ) : Fintype (Coordinate n) :=
  Fintype.ofInjective
    (fun s : Coordinate n =>
      (⟨s.val, Finset.mem_powerset.mpr s.property.2⟩ :
        {s : Finset ℕ // s ∈ (Finset.range n).powerset}))
    (by
      intro s t h
      apply Subtype.ext
      exact congrArg
        (fun u : {s : Finset ℕ // s ∈ (Finset.range n).powerset} => u.val) h)

variable (A : ℕ → Type)

def Level (i n : ℕ) := (s : Coordinate n) → A (i + s.val.card)

noncomputable instance levelFintype [∀ j, Fintype (A j)] (i n : ℕ) :
    Fintype (Level A i n) := inferInstanceAs (Fintype ((s : Coordinate n) → _))

noncomputable instance levelNonempty [∀ j, Nonempty (A j)] (i n : ℕ) :
    Nonempty (Level A i n) := by
  classical
  exact ⟨fun s => Classical.choice (inferInstance : Nonempty (A (i + s.val.card)))⟩

structure Node (i : ℕ) where
  height : ℕ
  table : Level A i height

namespace Level

variable {A} {i m n : ℕ}

def restrict (t : Level A i n) (h : m ≤ n) : Level A i m :=
  fun s => t (s.inclusion h)

@[simp] theorem restrict_apply (t : Level A i n) (h : m ≤ n)
    (s : Coordinate m) : t.restrict h s = t (s.inclusion h) := rfl

@[simp] theorem restrict_refl (t : Level A i n) :
    t.restrict (Nat.le_refl n) = t := by
  funext s
  rfl

@[simp] theorem restrict_restrict {k : ℕ} (t : Level A i n)
    (hm : m ≤ n) (hk : k ≤ m) :
    (t.restrict hm).restrict hk = t.restrict (hk.trans hm) := by
  funext s
  rfl

def singletonCoordinate (h : m < n) : Coordinate n :=
  ⟨{m}, by simp, by simpa using h⟩

def singleton (t : Level A i n) (h : m < n) : A (i + 1) :=
  Finset.card_singleton m ▸ t (singletonCoordinate h)

def sliceCoordinate (h : m < n) (s : Coordinate m) : Coordinate n :=
  ⟨insert m s.val, by simp, by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_range.mpr h
    · exact Finset.mem_range.mpr
        ((Finset.mem_range.mp (s.property.2 hx)).trans h)⟩

theorem sliceCoordinate_card (h : m < n) (s : Coordinate m) :
    (sliceCoordinate h s).val.card = s.val.card + 1 := by
  apply Finset.card_insert_of_notMem
  intro hm
  exact (Nat.lt_irrefl m) (Finset.mem_range.mp (s.property.2 hm))

def slice (t : Level A i n) (h : m < n) : Level A (i + 1) m :=
  fun s => cast (congrArg A (by
    dsimp only [sliceCoordinate]
    rw [Finset.card_insert_of_notMem
      (fun hm => Nat.lt_irrefl m (Finset.mem_range.mp (s.property.2 hm)))]
    omega)) (t (sliceCoordinate h s))

theorem slice_restrict {k : ℕ} (t : Level A i n)
    (hk : k ≤ n) (hm : m < k) :
    (t.restrict hk).slice hm = t.slice (hm.trans_le hk) := by
  funext s
  rfl

theorem singleton_restrict {k : ℕ} (t : Level A i n)
    (hk : k ≤ n) (hm : m < k) :
    (t.restrict hk).singleton hm = t.singleton (hm.trans_le hk) := rfl

end Level

namespace Node

variable {A} {i : ℕ}

theorem mk_injective (n : ℕ) :
    Function.Injective (fun t : Level A i n => (Node.mk n t : Node A i)) := by
  intro s t h
  cases h
  rfl

def restrict (t : Node A i) (m : ℕ) (h : m ≤ t.height) : Node A i :=
  ⟨m, t.table.restrict h⟩

@[simp] theorem height_restrict (t : Node A i) (m : ℕ) (h : m ≤ t.height) :
    (t.restrict m h).height = m := rfl

theorem restrict_congr {s t : Node A i} (hst : s = t) (m : ℕ)
    (hs : m ≤ s.height) (ht : m ≤ t.height) :
    s.restrict m hs = t.restrict m ht := by
  cases hst
  rfl

@[simp] theorem restrict_refl (t : Node A i) :
    t.restrict t.height (Nat.le_refl t.height) = t := by
  cases t
  simp [restrict]

@[simp] theorem restrict_restrict (t : Node A i)
    (m k : ℕ) (hm : m ≤ t.height) (hk : k ≤ m) :
    (t.restrict m hm).restrict k hk = t.restrict k (hk.trans hm) := by
  simp [restrict]

def slice (t : Node A i) (m : ℕ) (h : m < t.height) : Node A (i + 1) :=
  ⟨m, t.table.slice h⟩

@[simp] theorem height_slice (t : Node A i) (m : ℕ) (h : m < t.height) :
    (t.slice m h).height = m := rfl

theorem slice_congr {s t : Node A i} (hst : s = t) (m : ℕ)
    (hs : m < s.height) (ht : m < t.height) :
    s.slice m hs = t.slice m ht := by
  cases hst
  rfl

def singleton (t : Node A i) (m : ℕ) (h : m < t.height) : A (i + 1) :=
  t.table.singleton h

def root (i : ℕ) : Node A i :=
  ⟨0, fun s => False.elim (by
    obtain ⟨a, ha⟩ := s.property.1
    have h := Finset.mem_range.mp (s.property.2 ha)
    omega)⟩

theorem height_zero_unique (t : Node A i) (h : t.height = 0) : t = root i := by
  cases t with
  | mk n f =>
    cases h
    congr
    funext s
    obtain ⟨a, ha⟩ := s.property.1
    have hh := s.property.2 ha
    simp at hh

def Prefix (s t : Node A i) : Prop :=
  ∃ h : s.height ≤ t.height, t.restrict s.height h = s

theorem prefix_refl (t : Node A i) : Prefix t t :=
  ⟨Nat.le_refl _, t.restrict_refl⟩

theorem prefix_height_le {s t : Node A i} (h : Prefix s t) :
    s.height ≤ t.height := h.choose

theorem prefix_trans {r s t : Node A i}
    (hrs : Prefix r s) (hst : Prefix s t) : Prefix r t := by
  obtain ⟨hrs, er⟩ := hrs
  obtain ⟨hst, es⟩ := hst
  refine ⟨hrs.trans hst, ?_⟩
  calc
    t.restrict r.height (hrs.trans hst) =
        (t.restrict s.height hst).restrict r.height hrs := by
      simp only [restrict_restrict]
    _ = r := by simpa only [es] using er

theorem prefix_antisymm {s t : Node A i}
    (hst : Prefix s t) (hts : Prefix t s) : s = t := by
  obtain ⟨h, e⟩ := hst
  have heights := Nat.le_antisymm h hts.choose
  simpa [heights] using e.symm

theorem prefix_eq_of_height_eq {s t : Node A i} (h : Prefix s t)
    (hh : s.height = t.height) : s = t := by
  obtain ⟨hl, he⟩ := h
  simpa [hh] using he.symm

end Node

end RelationalRamsey632.Source
