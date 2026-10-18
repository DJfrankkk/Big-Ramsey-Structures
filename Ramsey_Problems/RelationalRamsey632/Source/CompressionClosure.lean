import RelationalRamsey632.Source.LevelIndex

/-! Exact covariance of the least intrinsic closure under compression. -/

namespace RelationalRamsey632.Source

variable {A : ℕ → Type} {e : ℕ → ℕ} (he : StrictMono e)
    (E : (i : ℕ) → Set (Node A i)) (L : Set ℕ)
    (hclosed : Closed A E L)
    (hgrid : ∀ i t, t ∈ E i → ∃ n, t.height = e n)
    (hlevels : ∀ n ∈ L, ∃ k, n = e k)

include hclosed hgrid

theorem compressOn_meet {i : ℕ} {s t : Node A i} (hs : s ∈ E i) (ht : t ∈ E i) :
    compressOn e he (s.meet t) = (compressOn e he s).meet (compressOn e he t) := by
  cases s with
  | mk a s =>
    cases t with
    | mk b t =>
      obtain ⟨n, hn⟩ := hgrid i (Node.mk a s) hs
      obtain ⟨m, hm⟩ := hgrid i (Node.mk b t) ht
      dsimp only [Node.height] at hn hm
      subst a
      subst b
      exact compressOn_meet_mk he E L hclosed hgrid i n m s t hs ht

include hlevels

theorem compressed_family_closed :
    Closed A (fun i => compressOn e he '' E i) (levelIndex e '' L) where
  height := by
    rintro i p ⟨t, ht, rfl⟩
    exact ⟨t.height, hclosed.height i t ht, (compressOn_height e he t (hgrid i t ht)).symm⟩
  meet := by
    rintro i p q ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s.meet t, hclosed.meet i s t hs ht, compressOn_meet he E L hclosed hgrid hs ht⟩
  restrict := by
    rintro i p z ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ hle
    obtain ⟨k, hk⟩ := hlevels m hm
    subst m
    cases t with
    | mk a t =>
      obtain ⟨n, hn⟩ := hgrid i (Node.mk a t) ht
      dsimp only [Node.height] at hn
      subst a
      have hkn : k ≤ n := by
        simpa only [levelIndex_apply e he, compressOn_mk] using hle
      have hsrc := he.monotone hkn
      have hx := hclosed.restrict i (Node.mk (e n) t) (e k) ht hm hsrc
      refine ⟨(Node.mk (e n) t).restrict (e k) hsrc, hx, ?_⟩
      have hc := compressOn_restrict_mk e he i n k t hkn
      have heq := Node.restrict_congr (compressOn_mk e he i n t).symm k hkn
        (by simpa only [levelIndex_apply e he] using hle)
      simpa only [levelIndex_apply e he] using hc.trans heq
  slice := by
    rintro i p z ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ hlt
    obtain ⟨k, hk⟩ := hlevels m hm
    subst m
    cases t with
    | mk a t =>
      obtain ⟨n, hn⟩ := hgrid i (Node.mk a t) ht
      dsimp only [Node.height] at hn
      subst a
      have hkn : k < n := by
        simpa only [levelIndex_apply e he, compressOn_mk] using hlt
      have hsrc := he hkn
      have hx := hclosed.slice i (Node.mk (e n) t) (e k) ht hm hsrc
      refine ⟨(Node.mk (e n) t).slice (e k) hsrc, hx, ?_⟩
      have hc := compressOn_slice_mk e he i n k t hkn
      have heq := Node.slice_congr (compressOn_mk e he i n t).symm k hkn
        (by simpa only [levelIndex_apply e he] using hlt)
      simpa only [levelIndex_apply e he] using hc.trans heq

omit hclosed hgrid hlevels

noncomputable def compressionObject (x : SourceObject A) : SourceObject A :=
  match x with
  | .inl ⟨i, t⟩ => .inl ⟨i, compressOn e he t⟩
  | .inr n => .inr (levelIndex e n)

theorem generated_compression {X : Set (Node A 0)}
    (hgridX : ∀ i t, t ∈ closureNodes A X i → ∃ n, t.height = e n) :
    ∀ x, Generated A X x →
      Generated A (compressOn e he '' X) (compressionObject he x) := by
  intro x hx
  induction hx with
  | generator t ht => exact Generated.generator _ ⟨t, ht, rfl⟩
  | height t ht ih =>
    dsimp only [compressionObject]
    exact (compressOn_height e he t (hgridX _ t ht)) ▸ Generated.height _ ih
  | meet s t hs ht ihs iht =>
    dsimp only [compressionObject]
    exact (compressOn_meet he (closureNodes A X) (closureLevels A X)
      (generatedClosure_closed A X) hgridX hs ht).symm ▸
        Generated.meet _ _ ihs iht
  | restrict t m ht hm h iht ihm =>
    obtain ⟨j, u, hu, hju⟩ := closureLevels_node_witness A hm
    obtain ⟨k, hk⟩ := hgridX j u hu
    have hmk : m = e k := hju.symm.trans hk
    clear hju
    subst m
    cases t with
    | mk a t =>
      obtain ⟨n, hn⟩ := hgridX _ (Node.mk a t) ht
      dsimp only [Node.height] at hn
      subst a
      have hkn : k ≤ n := he.le_iff_le.mp h
      dsimp only [compressionObject] at iht ihm ⊢
      simp only [compressOn_mk] at iht
      simp only [levelIndex_apply e he] at ihm
      have hg := Generated.restrict (Node.mk n (t.sample e he)) k iht ihm hkn
      exact (compressOn_restrict_mk e he _ n k t hkn).symm ▸ hg
  | slice t m ht hm h iht ihm =>
    obtain ⟨j, u, hu, hju⟩ := closureLevels_node_witness A hm
    obtain ⟨k, hk⟩ := hgridX j u hu
    have hmk : m = e k := hju.symm.trans hk
    clear hju
    subst m
    cases t with
    | mk a t =>
      obtain ⟨n, hn⟩ := hgridX _ (Node.mk a t) ht
      dsimp only [Node.height] at hn
      subst a
      have hkn : k < n := he.lt_iff_lt.mp h
      dsimp only [compressionObject] at iht ihm ⊢
      simp only [compressOn_mk] at iht
      simp only [levelIndex_apply e he] at ihm
      have hg := Generated.slice (Node.mk n (t.sample e he)) k iht ihm hkn
      exact (compressOn_slice_mk e he _ n k t hkn).symm ▸ hg

theorem compression_closure_covariance {X : Set (Node A 0)}
    (hgridX : ∀ i t, t ∈ closureNodes A X i → ∃ n, t.height = e n) :
    (∀ i, closureNodes A (compressOn e he '' X) i =
      compressOn e he '' closureNodes A X i) ∧
      closureLevels A (compressOn e he '' X) = levelIndex e '' closureLevels A X := by
  have hlevelGrid : ∀ n ∈ closureLevels A X, ∃ k, n = e k := by
    intro n hn
    obtain ⟨i, t, ht, hh⟩ := closureLevels_node_witness A hn
    obtain ⟨k, hk⟩ := hgridX i t ht
    exact ⟨k, hh.symm.trans hk⟩
  have hleast := generatedClosure_least A (compressOn e he '' X)
    (fun i => compressOn e he '' closureNodes A X i)
    (levelIndex e '' closureLevels A X)
    (compressed_family_closed he (closureNodes A X) (closureLevels A X)
      (generatedClosure_closed A X) hgridX hlevelGrid) (by
        rintro t ⟨s, hs, rfl⟩
        exact ⟨s, Generated.generator s hs, rfl⟩)
  constructor
  · intro i
    apply Set.Subset.antisymm (hleast.1 i)
    rintro t ⟨s, hs, rfl⟩
    exact generated_compression he hgridX _ hs
  · apply Set.Subset.antisymm hleast.2
    rintro n ⟨m, hm, rfl⟩
    exact generated_compression he hgridX _ hm

end RelationalRamsey632.Source
