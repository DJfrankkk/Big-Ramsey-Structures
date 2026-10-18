import RelationalRamsey632.Source.NormalFormHeredity

/-! Height comparisons and exact retained-coordinate evaluations on markers. -/

namespace RelationalRamsey632.Source

theorem canonicalCompression_height_recover {A : ℕ → Type} (L : Finset ℕ)
    {i : ℕ} (t : Node A i) (ht : t.height ∈ L) :
    levelEnumeration L (canonicalCompression L t).height = t.height := by
  have h := levelEnumeration_range_contains L ht
  unfold canonicalCompression
  rw [compressOn_height (levelEnumeration L) (levelEnumeration_strictMono L) t h]
  exact (levelIndex_spec (levelEnumeration L) h).symm

theorem canonicalCompression_height_le_iff {A : ℕ → Type} (L : Finset ℕ)
    {i j : ℕ} (s : Node A i) (t : Node A j) (hs : s.height ∈ L) (ht : t.height ∈ L) :
    (canonicalCompression L s).height ≤ (canonicalCompression L t).height ↔
      s.height ≤ t.height := by
  have h := (levelEnumeration_strictMono L).le_iff_le
    (a := (canonicalCompression L s).height) (b := (canonicalCompression L t).height)
  rw [canonicalCompression_height_recover L s hs,
    canonicalCompression_height_recover L t ht] at h
  exact h.symm

theorem canonicalCompression_height_lt_iff {A : ℕ → Type} (L : Finset ℕ)
    {i j : ℕ} (s : Node A i) (t : Node A j) (hs : s.height ∈ L) (ht : t.height ∈ L) :
    (canonicalCompression L s).height < (canonicalCompression L t).height ↔
      s.height < t.height := by
  have h := (levelEnumeration_strictMono L).lt_iff_lt
    (a := (canonicalCompression L s).height) (b := (canonicalCompression L t).height)
  rw [canonicalCompression_height_recover L s hs,
    canonicalCompression_height_recover L t ht] at h
  exact h.symm

theorem marked_height_mem {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (j : Fin b) : (v j).2.height ∈ tupleLevels v := by
  change (v j).2.height ∈ (tupleLevels v : Set ℕ)
  rw [tupleLevels_coe]
  exact Generated.height _ (Generated.generator _ ⟨j, rfl⟩)

theorem normalForm_height_lt_iff {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (j k : Fin b) :
    (normalForm v j).2.height < (normalForm v k).2.height ↔
      (v j).2.height < (v k).2.height :=
  canonicalCompression_height_lt_iff (tupleLevels v) (v j).2 (v k).2
    (marked_height_mem v j) (marked_height_mem v k)

theorem normalForm_height_le_iff {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (j k : Fin b) :
    (normalForm v j).2.height ≤ (normalForm v k).2.height ↔
      (v j).2.height ≤ (v k).2.height :=
  canonicalCompression_height_le_iff (tupleLevels v) (v j).2 (v k).2
    (marked_height_mem v j) (marked_height_mem v k)

theorem node_evaluation_heq {A : ℕ → Type} {i : ℕ} {s t : Node A i} (h : s = t)
    (c : Coordinate s.height) (d : Coordinate t.height) (hcd : c.val = d.val) :
    HEq (s.table c) (t.table d) := by
  cases h
  exact Level.apply_heq s.table (Subtype.ext hcd)

/-- Exact decoding API: a compressed retained coordinate evaluates to its
original value once its coordinate set is unranked by the level enumeration. -/
theorem canonicalCompression_evaluation {A : ℕ → Type} (L : Finset ℕ)
    {i : ℕ} (t : Node A i) (ht : t.height ∈ L)
    (c : Coordinate t.height) (d : Coordinate (canonicalCompression L t).height)
    (hcoords : d.val.image (levelEnumeration L) = c.val) :
    HEq ((canonicalCompression L t).table d) (t.table c) := by
  cases t with
  | mk a t =>
    obtain ⟨n, hn⟩ := levelEnumeration_range_contains L ht
    dsimp only [Node.height] at hn
    subst a
    have hc : canonicalCompression L (Node.mk (levelEnumeration L n) t) =
        Node.mk n (t.sample (levelEnumeration L) (levelEnumeration_strictMono L)) :=
      compressOn_mk (levelEnumeration L) (levelEnumeration_strictMono L) i n t
    let d' : Coordinate n := ⟨d.val, d.property.1, by
      have hheight := congrArg Node.height hc
      change (canonicalCompression L (Node.mk (levelEnumeration L n) t)).height = n at hheight
      intro x hx
      exact Finset.mem_range.mpr
        ((Finset.mem_range.mp (d.property.2 hx)).trans_le hheight.le)⟩
    have h1 := node_evaluation_heq hc d d' rfl
    have h2 := Level.sample_apply_heq (levelEnumeration L) (levelEnumeration_strictMono L) t d'
    have h3 :
        (d'.sample (levelEnumeration L) (levelEnumeration_strictMono L)) = c :=
      Subtype.ext hcoords
    exact h1.trans (h2.trans (Level.apply_heq t h3))

end RelationalRamsey632.Source
