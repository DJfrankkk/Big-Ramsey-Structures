import RelationalRamsey632.Source.Valuations

/-! Exact covariance of the intrinsic least closure under constructed valuations. -/

namespace RelationalRamsey632.Source

namespace StrongVector

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he)

noncomputable def mapObject (x : SourceObject A) : SourceObject A :=
  match x with
  | .inl ⟨i, t⟩ => .inl ⟨i, S.mapNode t⟩
  | .inr n => .inr (e n)

theorem generated_map {X : Set (Node A 0)} :
    ∀ x, Generated A X x →
      Generated A (S.mapNode '' X) (S.mapObject x) := by
  intro x hx
  induction hx with
  | generator t ht =>
    exact Generated.generator (S.mapNode t) ⟨t, ht, rfl⟩
  | height t ht ih =>
    exact Generated.height (S.mapNode t) ih
  | meet s t hs ht ihs iht =>
    simpa only [mapObject, S.mapNode_meet] using
      Generated.meet (S.mapNode s) (S.mapNode t) ihs iht
  | restrict t n ht hn h iht ihn =>
    dsimp only [mapObject]
    exact (S.mapNode_restrict t n h) ▸
      Generated.restrict (S.mapNode t) (e n) iht ihn (he.monotone h)
  | slice t n ht hn h iht ihn =>
    dsimp only [mapObject]
    exact (S.mapNode_slice t n h) ▸
      Generated.slice (S.mapNode t) (e n) iht ihn (he h)

theorem image_closure_closed (X : Set (Node A 0)) :
    Closed A
      (fun i => S.mapNode '' closureNodes A X i)
      (e '' closureLevels A X) where
  height := by
    rintro i p ⟨t, ht, rfl⟩
    exact ⟨t.height, Generated.height t ht, rfl⟩
  meet := by
    rintro i p q ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s.meet t, Generated.meet s t hs ht, (S.mapNode_meet s t).symm⟩
  restrict := by
    rintro i p n ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ hle
    have h : m ≤ t.height := he.le_iff_le.mp hle
    exact ⟨t.restrict m h, Generated.restrict t m ht hm h,
      (S.mapNode_restrict t m h).symm⟩
  slice := by
    rintro i p n ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ hlt
    have h : m < t.height := he.lt_iff_lt.mp hlt
    exact ⟨t.slice m h, Generated.slice t m ht hm h,
      (S.mapNode_slice t m h).symm⟩

theorem closure_covariance (X : Set (Node A 0)) :
    (∀ i, closureNodes A (S.mapNode '' X) i =
      S.mapNode '' closureNodes A X i) ∧
      closureLevels A (S.mapNode '' X) = e '' closureLevels A X := by
  have hleast := generatedClosure_least A (S.mapNode '' X)
    (fun i => S.mapNode '' closureNodes A X i)
    (e '' closureLevels A X) (S.image_closure_closed X) (by
      rintro t ⟨s, hs, rfl⟩
      exact ⟨s, Generated.generator s hs, rfl⟩)
  constructor
  · intro i
    apply Set.Subset.antisymm (hleast.1 i)
    rintro p ⟨t, ht, rfl⟩
    exact S.generated_map _ ht
  · apply Set.Subset.antisymm hleast.2
    rintro n ⟨m, hm, rfl⟩
    exact S.generated_map _ hm

end StrongVector

end RelationalRamsey632.Source
