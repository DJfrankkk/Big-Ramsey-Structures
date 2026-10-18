import RelationalRamsey632.Source.Sampling

/-! One step is faithfully specified by predecessor, singleton, and full slice. -/

namespace RelationalRamsey632.Source

namespace Coordinate

def lower {n : ℕ} (s : Coordinate (n + 1)) (hn : n ∉ s.val) : Coordinate n :=
  ⟨s.val, s.property.1, by
    intro x hx
    have hx' := Finset.mem_range.mp (s.property.2 hx)
    have hne : x ≠ n := fun he => hn (he ▸ hx)
    exact Finset.mem_range.mpr (by omega)⟩

def eraseTop {n : ℕ} (s : Coordinate (n + 1))
    (hs : (s.val.erase n).Nonempty) : Coordinate n :=
  ⟨s.val.erase n, hs, by
    intro x hx
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    have hx' := Finset.mem_range.mp (s.property.2 hx)
    exact Finset.mem_range.mpr (by omega)⟩

theorem insert_eraseTop {n : ℕ} (s : Coordinate (n + 1)) (hn : n ∈ s.val)
    (hs : (s.val.erase n).Nonempty) :
    Level.sliceCoordinate (Nat.lt_succ_self n) (s.eraseTop hs) = s := by
  apply Subtype.ext
  exact Finset.insert_erase hn

theorem singleton_of_eraseTop_empty {n : ℕ} (s : Coordinate (n + 1))
    (hs : ¬ (s.val.erase n).Nonempty) :
    s = Level.singletonCoordinate (Nat.lt_succ_self n) := by
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hs
  have hsingle := (Finset.erase_eq_empty_iff s.val n).mp hempty
  apply Subtype.ext
  exact hsingle.resolve_left s.property.1.ne_empty

end Coordinate

namespace Level

variable {A : ℕ → Type} {i n : ℕ}

def extend (p : Level A i n) (a : A (i + 1)) (v : Level A (i + 1) n) :
    Level A i (n + 1) :=
  fun c =>
    if hn : n ∈ c.val then
      if hc : (c.val.erase n).Nonempty then
        cast (congrArg A (by
          have hcard := Finset.card_erase_add_one hn
          change i + 1 + (c.val.erase n).card = i + c.val.card
          omega)) (v (c.eraseTop hc))
      else
        cast (congrArg A (by
          have he := congrArg Subtype.val (c.singleton_of_eraseTop_empty hc)
          change i + 1 = i + c.val.card
          rw [he]
          rfl)) a
    else p (c.lower hn)

@[simp] theorem extend_restrict (p : Level A i n) (a : A (i + 1))
    (v : Level A (i + 1) n) :
    (extend p a v).restrict (Nat.le_succ n) = p := by
  funext c
  have hn : n ∉ (c.inclusion (Nat.le_succ n)).val := by
    intro h
    exact Nat.lt_irrefl n (Finset.mem_range.mp (c.property.2 h))
  simp only [restrict, extend, dif_neg hn]
  rfl

@[simp] theorem extend_singleton (p : Level A i n) (a : A (i + 1))
    (v : Level A (i + 1) n) :
    (extend p a v).singleton (Nat.lt_succ_self n) = a := by
  simp [singleton, extend, singletonCoordinate]
  apply eq_of_heq
  exact cast_heq _ _

@[simp] theorem extend_slice (p : Level A i n) (a : A (i + 1))
    (v : Level A (i + 1) n) :
    (extend p a v).slice (Nat.lt_succ_self n) = v := by
  funext c
  let s := sliceCoordinate (Nat.lt_succ_self n) c
  have hnot : n ∉ c.val := by
    intro h
    exact Nat.lt_irrefl n (Finset.mem_range.mp (c.property.2 h))
  have hn : n ∈ s.val := Finset.mem_insert_self _ _
  have he : s.val.erase n = c.val := Finset.erase_insert hnot
  have hc : (s.val.erase n).Nonempty := he.symm ▸ c.property.1
  have hec : s.eraseTop hc = c := Subtype.ext he
  apply eq_of_heq
  have h1 : HEq ((extend p a v).slice (Nat.lt_succ_self n) c)
      ((extend p a v) s) := cast_heq _ _
  have h2 : HEq ((extend p a v) s) (v (s.eraseTop hc)) := by
    unfold extend
    simp only [dif_pos hn, dif_pos hc]
    exact cast_heq _ _
  exact h1.trans (h2.trans (apply_heq v hec))

/-- Ambient immediate successor values are completely determined by these
three components, including the entire next-sort slice. -/
theorem successor_ext (s t : Level A i (n + 1))
    (hp : s.restrict (Nat.le_succ n) = t.restrict (Nat.le_succ n))
    (ha : s.singleton (Nat.lt_succ_self n) = t.singleton (Nat.lt_succ_self n))
    (hv : s.slice (Nat.lt_succ_self n) = t.slice (Nat.lt_succ_self n)) :
    s = t := by
  funext c
  by_cases hn : n ∈ c.val
  · by_cases hc : (c.val.erase n).Nonempty
    · have he := congrFun hv (c.eraseTop hc)
      have hs : HEq (s.slice (Nat.lt_succ_self n) (c.eraseTop hc))
          (s (sliceCoordinate (Nat.lt_succ_self n) (c.eraseTop hc))) :=
        cast_heq _ _
      have ht : HEq (t.slice (Nat.lt_succ_self n) (c.eraseTop hc))
          (t (sliceCoordinate (Nat.lt_succ_self n) (c.eraseTop hc))) :=
        cast_heq _ _
      have h := hs.symm.trans ((heq_of_eq he).trans ht)
      have hcoord := c.insert_eraseTop hn hc
      have h' : HEq (s c) (t c) :=
        (apply_heq s hcoord.symm).trans (h.trans (apply_heq t hcoord))
      exact eq_of_heq h'
    · have hcoord := c.singleton_of_eraseTop_empty hc
      subst c
      exact ha
  · exact congrFun hp (c.lower hn)

theorem successor_existsUnique (p : Level A i n) (a : A (i + 1))
    (v : Level A (i + 1) n) :
    ∃! t : Level A i (n + 1),
      t.restrict (Nat.le_succ n) = p ∧
      t.singleton (Nat.lt_succ_self n) = a ∧
      t.slice (Nat.lt_succ_self n) = v := by
  refine ⟨extend p a v, ⟨extend_restrict p a v,
    extend_singleton p a v, extend_slice p a v⟩, ?_⟩
  intro t ht
  apply successor_ext
  · exact ht.1.trans (extend_restrict p a v).symm
  · exact ht.2.1.trans (extend_singleton p a v).symm
  · exact ht.2.2.trans (extend_slice p a v).symm

end Level

end RelationalRamsey632.Source
