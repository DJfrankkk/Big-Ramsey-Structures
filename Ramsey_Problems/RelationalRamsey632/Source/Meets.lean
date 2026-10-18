import RelationalRamsey632.Source.Nodes
import Mathlib.Data.Finset.Max

/-! Greatest common restrictions of the actual source nodes. -/

namespace RelationalRamsey632.Source

namespace Node

variable {A : ℕ → Type} {i : ℕ}

def CommonHeight (s t : Node A i) (n : ℕ) : Prop :=
  ∃ (hs : n ≤ s.height) (ht : n ≤ t.height),
    s.restrict n hs = t.restrict n ht

theorem commonHeight_zero (s t : Node A i) : CommonHeight s t 0 := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
  exact (height_zero_unique _ rfl).trans (height_zero_unique _ rfl).symm

noncomputable def commonHeights (s t : Node A i) : Finset ℕ := by
  classical
  exact (Finset.range (min s.height t.height + 1)).filter (CommonHeight s t)

theorem mem_commonHeights (s t : Node A i) (n : ℕ) :
    n ∈ commonHeights s t ↔ CommonHeight s t n := by
  classical
  simp only [commonHeights, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hs, ht, he⟩
    exact ⟨by omega, hs, ht, he⟩

theorem commonHeights_nonempty (s t : Node A i) :
    (commonHeights s t).Nonempty :=
  ⟨0, (mem_commonHeights s t 0).mpr (commonHeight_zero s t)⟩

noncomputable def meetHeight (s t : Node A i) : ℕ :=
  (commonHeights s t).max' (commonHeights_nonempty s t)

theorem commonHeight_meetHeight (s t : Node A i) :
    CommonHeight s t (meetHeight s t) :=
  (mem_commonHeights s t _).mp (Finset.max'_mem _ _)

theorem meetHeight_le_left (s t : Node A i) :
    meetHeight s t ≤ s.height := (commonHeight_meetHeight s t).choose

theorem meetHeight_le_right (s t : Node A i) :
    meetHeight s t ≤ t.height := (commonHeight_meetHeight s t).choose_spec.choose

theorem commonHeight_le_meetHeight {s t : Node A i} {n : ℕ}
    (h : CommonHeight s t n) : n ≤ meetHeight s t :=
  Finset.le_max' _ _ ((mem_commonHeights s t n).mpr h)

noncomputable def meet (s t : Node A i) : Node A i :=
  s.restrict (meetHeight s t) (meetHeight_le_left s t)

@[simp] theorem height_meet (s t : Node A i) :
    (meet s t).height = meetHeight s t := rfl

theorem restrict_prefix (t : Node A i) (n : ℕ) (h : n ≤ t.height) :
    Prefix (t.restrict n h) t := ⟨h, rfl⟩

theorem meet_prefix_left (s t : Node A i) : Prefix (meet s t) s :=
  restrict_prefix s _ _

theorem meet_prefix_right (s t : Node A i) : Prefix (meet s t) t := by
  obtain ⟨hs, ht, he⟩ := commonHeight_meetHeight s t
  exact ⟨ht, he.symm⟩

theorem commonHeight_of_common_prefix {s t u : Node A i}
    (hus : Prefix u s) (hut : Prefix u t) : CommonHeight s t u.height := by
  obtain ⟨hs, es⟩ := hus
  obtain ⟨ht, et⟩ := hut
  exact ⟨hs, ht, es.trans et.symm⟩

theorem commonHeight_downward {s t : Node A i} {m n : ℕ}
    (h : CommonHeight s t n) (hmn : m ≤ n) : CommonHeight s t m := by
  obtain ⟨hs, ht, he⟩ := h
  have hsu : Prefix (s.restrict n hs) s := restrict_prefix s n hs
  have htu : Prefix (s.restrict n hs) t := ⟨ht, he.symm⟩
  have hpre := restrict_prefix (s.restrict n hs) m hmn
  exact commonHeight_of_common_prefix (prefix_trans hpre hsu) (prefix_trans hpre htu)

theorem common_prefix_prefix_meet {s t u : Node A i}
    (hus : Prefix u s) (hut : Prefix u t) : Prefix u (meet s t) := by
  obtain ⟨hs, es⟩ := hus
  obtain ⟨ht, et⟩ := hut
  have hm : u.height ≤ meetHeight s t :=
    commonHeight_le_meetHeight ⟨hs, ht, es.trans et.symm⟩
  refine ⟨hm, ?_⟩
  simpa only [meet, restrict_restrict] using es

theorem meet_comm (s t : Node A i) : meet s t = meet t s :=
  prefix_antisymm
    (common_prefix_prefix_meet (meet_prefix_right s t) (meet_prefix_left s t))
    (common_prefix_prefix_meet (meet_prefix_right t s) (meet_prefix_left t s))

@[simp] theorem meet_self (s : Node A i) : meet s s = s :=
  prefix_antisymm (meet_prefix_left s s)
    (common_prefix_prefix_meet (prefix_refl s) (prefix_refl s))

theorem meet_eq_left_of_prefix {s t : Node A i} (h : Prefix s t) : meet s t = s :=
  prefix_antisymm (meet_prefix_left s t)
    (common_prefix_prefix_meet (prefix_refl s) h)

theorem meetHeight_lt_of_incomparable {s t : Node A i}
    (hst : ¬ Prefix s t) (hts : ¬ Prefix t s) :
    meetHeight s t < min s.height t.height := by
  have hs := meetHeight_le_left s t
  have ht := meetHeight_le_right s t
  have hneS : meetHeight s t ≠ s.height := by
    intro he
    have h := meet_prefix_right s t
    have hm : meet s t = s := by simp [meet, he]
    exact hst (hm ▸ h)
  have hneT : meetHeight s t ≠ t.height := by
    intro he
    obtain ⟨h1, h2, hh⟩ := commonHeight_meetHeight s t
    have hm : meet s t = t := by simpa only [meet, he, restrict_refl] using hh
    exact hts (hm ▸ meet_prefix_left s t)
  omega

end Node

end RelationalRamsey632.Source
