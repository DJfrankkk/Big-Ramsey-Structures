import RelationalRamsey632.Source.CompressionClosure

namespace RelationalRamsey632.Source

theorem levelIndex_enumeration_image (L : Finset ℕ) :
    levelIndex (levelEnumeration L) '' (L : Set ℕ) = (Finset.range L.card : Set ℕ) := by
  apply Set.Subset.antisymm
  · rintro n ⟨m, hm, heq⟩
    obtain ⟨k, hk⟩ := levelEnumeration_range_contains L hm
    have hkL : k < L.card :=
      (levelEnumeration_mem_iff L k).mp (hk ▸ hm)
    rw [hk, levelIndex_apply _ (levelEnumeration_strictMono L)] at heq
    subst n
    exact Finset.mem_range.mpr hkL
  · intro n hn
    have hn' : n < L.card := Finset.mem_range.mp hn
    exact ⟨levelEnumeration L n, (levelEnumeration_mem_iff L n).mpr hn',
      levelIndex_apply _ (levelEnumeration_strictMono L) n⟩

theorem canonical_compression_closure {A : ℕ → Type} {X : Set (Node A 0)}
    (L : Finset ℕ) (hL : closureLevels A X = (L : Set ℕ)) :
    (∀ i, closureNodes A (canonicalCompression L '' X) i =
      canonicalCompression L '' closureNodes A X i) ∧
      closureLevels A (canonicalCompression L '' X) = (Finset.range L.card : Set ℕ) := by
  have hcov := compression_closure_covariance
    (levelEnumeration_strictMono L) (closure_levels_on_grid L hL)
  constructor
  · exact hcov.1
  · exact hcov.2.trans (by rw [hL]; exact levelIndex_enumeration_image L)

theorem table_cast_apply_heq {A : ℕ → Type} {i m n : ℕ} (h : m = n)
    (t : Level A i m) (c : Coordinate m) (d : Coordinate n)
    (hcd : c.val = d.val) :
    HEq (t c) ((cast (congrArg (Level A i) h) t) d) := by
  cases h
  exact Level.apply_heq t (Subtype.ext hcd)

theorem node_mk_cast {A : ℕ → Type} {i m n : ℕ} (h : m = n)
    (t : Level A i m) :
    (Node.mk n (cast (congrArg (Level A i) h) t) : Node A i) = Node.mk m t := by
  cases h
  rfl

theorem compressOn_identity_below {A : ℕ → Type} {e : ℕ → ℕ} (he : StrictMono e)
    (i n : ℕ) (hbelow : ∀ k, k ≤ n → e k = k) (t : Level A i n) :
    compressOn e he (Node.mk n t) = Node.mk n t := by
  have hn : n = e n := (hbelow n le_rfl).symm
  let u : Level A i (e n) := cast (congrArg (Level A i) hn) t
  have hs : u.sample e he = t := by
    funext c
    have hcd : c.val = (c.sample e he).val := by
      change c.val = c.val.image e
      symm
      calc
        c.val.image e = c.val.image id := Finset.image_congr (by
          intro x hx
          exact hbelow x (Nat.le_of_lt (Finset.mem_range.mp (c.property.2 hx))))
        _ = c.val := Finset.image_id
    apply eq_of_heq
    exact (Level.sample_apply_heq e he u c).trans
      (table_cast_apply_heq hn t c (c.sample e he) hcd).symm
  calc
    compressOn e he (Node.mk n t) = compressOn e he (Node.mk (e n) u) :=
      congrArg (compressOn e he) (node_mk_cast hn t).symm
    _ = Node.mk n (u.sample e he) := compressOn_mk e he i n u
    _ = Node.mk n t := congrArg (Node.mk n) hs

theorem levelEnumeration_range_initial (H n : ℕ) (hn : n < H) :
    levelEnumeration (Finset.range H) n = n := by
  have hu : (fun j : Fin (Finset.range H).card => j.val) =
      (Finset.range H).orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl
      (fun j => Finset.mem_range.mpr (by simpa only [Finset.card_range] using j.isLt))
      (fun _ _ h => h)
  have hn' : n < (Finset.range H).card := by simpa only [Finset.card_range] using hn
  rw [levelEnumeration_initial _ hn']
  exact (congrFun hu ⟨n, hn'⟩).symm

theorem canonicalCompression_range_identity {A : ℕ → Type} (H : ℕ)
    {i : ℕ} (t : Node A i) (ht : t.height < H) :
    canonicalCompression (Finset.range H) t = t := by
  cases t with
  | mk n t =>
    apply compressOn_identity_below (levelEnumeration_strictMono (Finset.range H)) i n
    intro k hk
    exact levelEnumeration_range_initial H k (Nat.lt_of_le_of_lt hk ht)

theorem canonicalCompression_height_bound {A : ℕ → Type} (L : Finset ℕ)
    {i : ℕ} (t : Node A i) (ht : t.height ∈ L) :
    (canonicalCompression L t).height < L.card := by
  obtain ⟨n, hn⟩ := levelEnumeration_range_contains L ht
  have hmem : n < L.card := (levelEnumeration_mem_iff L n).mp (hn ▸ ht)
  have hht := compressOn_height (levelEnumeration L) (levelEnumeration_strictMono L) t ⟨n, hn⟩
  have hi : levelIndex (levelEnumeration L) t.height = n := by
    rw [hn, levelIndex_apply _ (levelEnumeration_strictMono L)]
  exact hht.trans hi ▸ hmem

end RelationalRamsey632.Source
