import RelationalRamsey632.Source.Rank

/-! Alphabet-typed sampling along an arbitrary strictly increasing level map. -/

namespace RelationalRamsey632.Source

namespace Coordinate

def sample (e : ℕ → ℕ) (he : StrictMono e) {n : ℕ}
    (s : Coordinate n) : Coordinate (e n) :=
  ⟨s.val.image e, s.property.1.image e, by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (he (Finset.mem_range.mp (s.property.2 ha)))⟩

@[simp] theorem sample_val (e : ℕ → ℕ) (he : StrictMono e) {n : ℕ}
    (s : Coordinate n) : (s.sample e he).val = s.val.image e := rfl

@[simp] theorem sample_card (e : ℕ → ℕ) (he : StrictMono e) {n : ℕ}
    (s : Coordinate n) : (s.sample e he).val.card = s.val.card :=
  Finset.card_image_of_injective s.val he.injective

theorem sample_inclusion (e : ℕ → ℕ) (he : StrictMono e)
    {m n : ℕ} (h : m ≤ n) (s : Coordinate m) :
    (s.inclusion h).sample e he = (s.sample e he).inclusion (he.monotone h) := by
  apply Subtype.ext
  rfl

theorem sample_sliceCoordinate (e : ℕ → ℕ) (he : StrictMono e)
    {m n : ℕ} (h : m < n) (s : Coordinate m) :
    (Level.sliceCoordinate h s).sample e he =
      Level.sliceCoordinate (he h) (s.sample e he) := by
  apply Subtype.ext
  exact Finset.image_insert e m s.val

theorem sample_singletonCoordinate (e : ℕ → ℕ) (he : StrictMono e)
    {m n : ℕ} (h : m < n) :
    (Level.singletonCoordinate h).sample e he =
      Level.singletonCoordinate (he h) := by
  apply Subtype.ext
  exact Finset.image_singleton e m

end Coordinate

namespace Level

variable {A : ℕ → Type} {i m n : ℕ}

def sample (e : ℕ → ℕ) (he : StrictMono e) (t : Level A i (e n)) :
    Level A i n :=
  fun s => cast (congrArg A (congrArg (i + ·) (s.sample_card e he)))
    (t (s.sample e he))

theorem sample_apply_heq (e : ℕ → ℕ) (he : StrictMono e)
    (t : Level A i (e n)) (s : Coordinate n) :
    HEq (t.sample e he s) (t (s.sample e he)) := cast_heq _ _

theorem apply_heq (t : Level A i n) {s s' : Coordinate n} (h : s = s') :
    HEq (t s) (t s') := by
  cases h
  rfl

theorem sample_restrict (e : ℕ → ℕ) (he : StrictMono e)
    (t : Level A i (e n)) (h : m ≤ n) :
    (t.sample e he).restrict h =
      (t.restrict (he.monotone h)).sample e he := by
  funext s
  rfl

theorem sample_singleton (e : ℕ → ℕ) (he : StrictMono e)
    (t : Level A i (e n)) (h : m < n) :
    (t.sample e he).singleton h = t.singleton (he h) := by
  apply eq_of_heq
  have hl : HEq ((t.sample e he).singleton h)
      (t.sample e he (singletonCoordinate h)) := by
    unfold singleton
    rfl
  have hr : HEq (t.singleton (he h)) (t (singletonCoordinate (he h))) := by
    unfold singleton
    rfl
  exact hl.trans ((sample_apply_heq e he t (singletonCoordinate h)).trans
    ((apply_heq t (Coordinate.sample_singletonCoordinate e he h)).trans hr.symm))

theorem sample_slice (e : ℕ → ℕ) (he : StrictMono e)
    (t : Level A i (e n)) (h : m < n) :
    (t.sample e he).slice h = (t.slice (he h)).sample e he := by
  funext s
  apply eq_of_heq
  have hl : HEq ((t.sample e he).slice h s)
      (t.sample e he (sliceCoordinate h s)) := cast_heq _ _
  have hr : HEq ((t.slice (he h)).sample e he s)
      ((t.slice (he h)) (s.sample e he)) := sample_apply_heq e he _ s
  have hr' : HEq ((t.slice (he h)) (s.sample e he))
      (t (sliceCoordinate (he h) (s.sample e he))) := cast_heq _ _
  exact hl.trans ((sample_apply_heq e he t (sliceCoordinate h s)).trans
    ((apply_heq t (Coordinate.sample_sliceCoordinate e he h s)).trans
      (hr'.symm.trans hr.symm)))

end Level

end RelationalRamsey632.Source
