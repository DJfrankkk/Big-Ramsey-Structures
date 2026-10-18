import RelationalRamsey632.Source.FiniteValuations
import RelationalRamsey632.Source.ValuationSampling

namespace RelationalRamsey632.Source

theorem generated_weight_lt {A : ℕ → Type} {X : Set (Node A 0)} {h : ℕ}
    (hX : ∀ t ∈ X, t.height < h) :
    ∀ x, Generated A X x → SourceObject.weight A x < h := by
  intro x hx
  induction hx with
  | generator t ht => simpa [SourceObject.weight] using hX t ht
  | height t ht ih => dsimp [SourceObject.weight] at ih ⊢; omega
  | meet s t hs ht ihs iht =>
    have hh := Node.meetHeight_le_left s t
    dsimp [SourceObject.weight] at ihs ⊢
    omega
  | restrict t n ht hn hle iht ihn =>
    dsimp [SourceObject.weight] at iht ⊢
    omega
  | slice t n ht hn hlt iht ihn =>
    dsimp [SourceObject.weight] at iht ⊢
    omega

namespace FiniteStrongVector

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e} {h : ℕ}
    (V : FiniteStrongVector A e he h)

noncomputable def mapNodeDefault {i : ℕ} (t : Node A i) : Node A i :=
  if hd : i + t.height < h then V.mapNode t hd else Node.root i

theorem mapNodeDefault_active {i : ℕ} (t : Node A i) (hd : i + t.height < h) :
    V.mapNodeDefault t = V.mapNode t hd := by
  simp only [mapNodeDefault, dif_pos hd]

theorem mapNodeDefault_height {i : ℕ} (t : Node A i) (hd : i + t.height < h) :
    (V.mapNodeDefault t).height = e t.height := by rw [V.mapNodeDefault_active t hd]; rfl

theorem mapNodeDefault_meet {i : ℕ} (s t : Node A i)
    (hs : i + s.height < h) (ht : i + t.height < h) :
    (V.mapNodeDefault s).meet (V.mapNodeDefault t) = V.mapNodeDefault (s.meet t) := by
  have hm : i + (s.meet t).height < h := by
    have hh := Node.meetHeight_le_left s t
    dsimp
    omega
  rw [V.mapNodeDefault_active s hs, V.mapNodeDefault_active t ht,
    V.mapNodeDefault_active (s.meet t) hm]
  exact V.mapNode_meet s t hs ht

theorem mapNodeDefault_restrict {i : ℕ} (t : Node A i) (hd : i + t.height < h)
    (m : ℕ) (hm : m ≤ t.height) :
    (V.mapNodeDefault t).restrict (e m) (by rw [V.mapNodeDefault_height t hd]; exact he.monotone hm)
      = V.mapNodeDefault (t.restrict m hm) := by
  have hmD : i + (t.restrict m hm).height < h := by dsimp; omega
  simp only [mapNodeDefault, dif_pos hd, dif_pos hmD]
  exact V.mapNode_restrict t hd m hm

theorem mapNodeDefault_slice {i : ℕ} (t : Node A i) (hd : i + t.height < h)
    (m : ℕ) (hm : m < t.height) :
    (V.mapNodeDefault t).slice (e m) (by rw [V.mapNodeDefault_height t hd]; exact he hm)
      = V.mapNodeDefault (t.slice m hm) := by
  have hmD : (i + 1) + (t.slice m hm).height < h := by dsimp; omega
  simp only [mapNodeDefault, dif_pos hd, dif_pos hmD]
  exact V.mapNode_slice t hd m hm

theorem finite_generated_map {X : Set (Node A 0)} (hX : ∀ t ∈ X, t.height < h) :
    ∀ x, Generated A X x → Generated A (V.mapNodeDefault '' X)
      (match x with
       | .inl ⟨i, t⟩ => .inl ⟨i, V.mapNodeDefault t⟩
       | .inr n => .inr (e n)) := by
  intro x hx
  induction hx with
  | generator t ht => exact Generated.generator _ ⟨t, ht, rfl⟩
  | height t ht ih =>
    have hd : _ + t.height < h := generated_weight_lt hX _ ht
    change Generated A (V.mapNodeDefault '' X) (.inr (e t.height))
    simpa only [V.mapNodeDefault_height t hd] using Generated.height _ ih
  | meet s t hs ht ihs iht =>
    have hsD : _ + s.height < h := generated_weight_lt hX _ hs
    have htD : _ + t.height < h := generated_weight_lt hX _ ht
    change Generated A (V.mapNodeDefault '' X) (.inl ⟨_, V.mapNodeDefault (s.meet t)⟩)
    simpa only [V.mapNodeDefault_meet s t hsD htD] using Generated.meet _ _ ihs iht
  | restrict t n ht hn hle iht ihn =>
    have hd : _ + t.height < h := generated_weight_lt hX _ ht
    change Generated A (V.mapNodeDefault '' X) (.inl ⟨_, V.mapNodeDefault (t.restrict n hle)⟩)
    simpa only [V.mapNodeDefault_restrict t hd n hle] using
      Generated.restrict _ _ iht ihn (by rw [V.mapNodeDefault_height t hd]; exact he.monotone hle)
  | slice t n ht hn hlt iht ihn =>
    have hd : _ + t.height < h := generated_weight_lt hX _ ht
    change Generated A (V.mapNodeDefault '' X) (.inl ⟨_, V.mapNodeDefault (t.slice n hlt)⟩)
    simpa only [V.mapNodeDefault_slice t hd n hlt] using
      Generated.slice _ _ iht ihn (by rw [V.mapNodeDefault_height t hd]; exact he hlt)

theorem finite_image_closure_closed (X : Set (Node A 0)) (hX : ∀ t ∈ X, t.height < h) :
    Closed A (fun i => V.mapNodeDefault '' closureNodes A X i) (e '' closureLevels A X) where
  height := by
    rintro i p ⟨t, ht, rfl⟩
    have hd : i + t.height < h := generated_weight_lt hX _ ht
    exact ⟨t.height, Generated.height t ht, (V.mapNodeDefault_height t hd).symm⟩
  meet := by
    rintro i p q ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have hsD : i + s.height < h := generated_weight_lt hX _ hs
    have htD : i + t.height < h := generated_weight_lt hX _ ht
    exact ⟨s.meet t, Generated.meet s t hs ht, (V.mapNodeDefault_meet s t hsD htD).symm⟩
  restrict := by
    rintro i p n ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ hle
    have hd : i + t.height < h := generated_weight_lt hX _ ht
    have hle' : m ≤ t.height := he.le_iff_le.mp ((V.mapNodeDefault_height t hd) ▸ hle)
    exact ⟨t.restrict m hle', Generated.restrict t m ht hm hle',
      (V.mapNodeDefault_restrict t hd m hle').symm⟩
  slice := by
    rintro i p n ⟨t, ht, rfl⟩ ⟨m, hm, rfl⟩ hlt
    have hd : i + t.height < h := generated_weight_lt hX _ ht
    have hlt' : m < t.height := he.lt_iff_lt.mp ((V.mapNodeDefault_height t hd) ▸ hlt)
    exact ⟨t.slice m hlt', Generated.slice t m ht hm hlt',
      (V.mapNodeDefault_slice t hd m hlt').symm⟩

theorem finite_closure_covariance (X : Set (Node A 0)) (hX : ∀ t ∈ X, t.height < h) :
    (∀ i, closureNodes A (V.mapNodeDefault '' X) i = V.mapNodeDefault '' closureNodes A X i) ∧
      closureLevels A (V.mapNodeDefault '' X) = e '' closureLevels A X := by
  have hl := generatedClosure_least A (V.mapNodeDefault '' X)
    (fun i => V.mapNodeDefault '' closureNodes A X i) (e '' closureLevels A X)
    (V.finite_image_closure_closed X hX) (by
      rintro t ⟨s, hs, rfl⟩
      exact ⟨s, Generated.generator s hs, rfl⟩)
  constructor
  · intro i
    apply Set.Subset.antisymm (hl.1 i)
    rintro t ⟨s, hs, rfl⟩
    exact V.finite_generated_map hX _ hs
  · apply Set.Subset.antisymm hl.2
    rintro n ⟨m, hm, rfl⟩
    exact V.finite_generated_map hX _ hm

theorem valuation_sample (n i : ℕ) (hd : i + n < h) (t : Level A i n) :
    (V.valuation n i hd t).sample e he = t := by
  induction n generalizing i with
  | zero =>
    funext c
    obtain ⟨x, hx⟩ := c.property.1
    have hh := c.property.2 hx
    simp at hh
  | succ n ih =>
    apply Level.successor_ext
    · simpa only [Level.sample_restrict, V.valuation_step_restrict] using
        ih i (by omega) (t.restrict (Nat.le_succ n))
    · exact (Level.sample_singleton e he (V.valuation (n + 1) i hd t)
        (Nat.lt_succ_self n)).trans (V.valuation_step_singleton n i hd t)
    · simpa only [Level.sample_slice, V.valuation_step_slice] using
        ih (i + 1) (by omega) (t.slice (Nat.lt_succ_self n))

theorem canonicalCompression_mapNode (L : Finset ℕ)
    {i : ℕ} (t : Node A i) (hd : i + t.height < h) (ht : t.height ∈ L) :
    canonicalCompression (L.image e) (V.mapNode t hd) = canonicalCompression L t := by
  cases t with
  | mk a t =>
    obtain ⟨n, hn⟩ := levelEnumeration_range_contains L ht
    dsimp only [Node.height] at hn
    subst a
    have hnL : n < L.card := (levelEnumeration_mem_iff L n).mp ht
    have hmarked := canonicalCompression_mk_of_range (L.image e)
      (e ∘ levelEnumeration L) (he.comp (levelEnumeration_strictMono L))
      L.card (StrongVector.levelImage_active_range (e := e) L) i n hnL
      (V.valuation (levelEnumeration L n) i hd t)
    dsimp only [Function.comp_apply] at hmarked
    change canonicalCompression (L.image e)
        (Node.mk (e (levelEnumeration L n)) (V.valuation (levelEnumeration L n) i hd t)) = _
    rw [hmarked]
    have hs := Level.sample_comp e (levelEnumeration L)
      he (levelEnumeration_strictMono L) i n (V.valuation (levelEnumeration L n) i hd t)
    rw [← hs, V.valuation_sample]
    exact (compressOn_mk (levelEnumeration L) (levelEnumeration_strictMono L) i n t).symm

noncomputable def mapVertices {U : Type} (v : U × Node A 0) : U × Node A 0 :=
  (v.1, V.mapNodeDefault v.2)

theorem mapVertices_projections {U : Type} {b : ℕ} (v : Fin b → U × Node A 0) :
    tupleProjections (V.mapVertices ∘ v) = V.mapNodeDefault '' tupleProjections v := by
  apply Set.Subset.antisymm
  · rintro t ⟨j, hj⟩
    exact ⟨(v j).2, ⟨j, rfl⟩, hj⟩
  · rintro t ⟨s, ⟨j, hj⟩, hs⟩
    exact ⟨j, (congrArg V.mapNodeDefault hj).trans hs⟩

theorem normalForm_mapVertices {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (hv : ∀ j, (v j).2.height < h) :
    normalForm (V.mapVertices ∘ v) = normalForm v := by
  have hX : ∀ t ∈ tupleProjections v, t.height < h := by
    rintro t ⟨j, rfl⟩
    exact hv j
  have hlevels : tupleLevels (V.mapVertices ∘ v) = (tupleLevels v).image e := by
    apply Finset.coe_injective
    rw [tupleLevels_coe, V.mapVertices_projections, (V.finite_closure_covariance _ hX).2,
      Finset.coe_image, tupleLevels_coe]
  funext j
  apply Prod.ext
  · rfl
  · change canonicalCompression (tupleLevels (V.mapVertices ∘ v)) (V.mapNodeDefault (v j).2)
        = canonicalCompression (tupleLevels v) (v j).2
    rw [hlevels, V.mapNodeDefault_active (v j).2 (by simpa using hv j)]
    apply V.canonicalCompression_mapNode
    change (v j).2.height ∈ (tupleLevels v : Set ℕ)
    rw [tupleLevels_coe]
    exact Generated.height _ (Generated.generator _ ⟨j, rfl⟩)

end FiniteStrongVector

end RelationalRamsey632.Source
