import CombinedRamsey.Revised20261018.Transfer

/-! The revised finite-stage lemma, in arbitrary relational languages.
Names always come from the initial pullback, not a subsequently refined
palette.  Original nullaries and repeated tuples are unrestricted. -/

namespace CombinedRamsey.Revised20261018.FiniteStage

open RelationalRamsey632 RelationalRamsey632.RelStructure
open RelationalRamsey632.Transfer RelationalRamsey632.Transfer.Named

variable {L S : Language} {X M J : Type} {n : J → ℕ}

def stage (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) :=
  (recodedSource a K B N φ).pullback (φ.comp η)

theorem stage_eq (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) :
    stage a N φ η = onStructure a K (N.pullback φ) K (N.pullback (φ.comp η)) := by
  unfold stage recodedSource
  rw [onStructure_pullback a K (N.pullback φ) B N (φ.comp η) (φ.comp η).injective,
    (φ.comp η).pullback_eq]

theorem stage_type (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K)
    {F : Type} {b : RelStructure L F} (e : RelEmbedding b K) :
    (stage a N φ η).pullback e =
      onStructure a K (N.pullback φ) b ((N.pullback (φ.comp η)).pullback e) := by
  rw [stage_eq, onStructure_pullback a K (N.pullback φ) K
    (N.pullback (φ.comp η)) e e.injective, e.pullback_eq]

theorem selected_type_iff (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K)
    (j : J) (hj : 0 < n j) (e f : RelEmbedding (a j) K) :
    (stage a N φ η).pullback e = (stage a N φ η).pullback f ↔
      (N.pullback (φ.comp η)).pullback e = (N.pullback (φ.comp η)).pullback f := by
  rw [stage_type, stage_type]
  constructor
  · intro h
    let p : palette (a j) K (N.pullback φ) :=
      ⟨(N.pullback (φ.comp η)).pullback e, ⟨η.comp e, rfl⟩⟩
    have hp : (onStructure a K (N.pullback φ) (a j) p.val).rel
        (name a K (N.pullback φ) j hj p) id :=
      (name_rel a K (N.pullback φ) (a j) p.val j hj p id).mpr
        ⟨Function.injective_id, rfl, rfl⟩
    have hq := h ▸ hp
    exact ((name_rel a K (N.pullback φ) (a j)
      ((N.pullback (φ.comp η)).pullback f) j hj p id).mp hq).2.2.symm
  · exact congrArg (onStructure a K (N.pullback φ) (a j))

noncomputable def selectedPaletteMap (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) (j : J) :
    palette (a j) K (N.pullback (φ.comp η)) → palette (a j) K (stage a N φ η) :=
  fun p => ⟨onStructure a K (N.pullback φ) (a j) p.val, by
    obtain ⟨e, he⟩ := p.property
    refine ⟨e, ?_⟩
    change (N.pullback (φ.comp η)).pullback e = p.val at he
    change (stage a N φ η).pullback e = onStructure a K (N.pullback φ) (a j) p.val
    rw [stage_type, he]⟩

theorem selectedPaletteMap_bijective (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) (j : J) (hj : 0 < n j) :
    Function.Bijective (selectedPaletteMap a N φ η j) := by
  constructor
  · rintro ⟨p, e, rfl⟩ ⟨q, f, rfl⟩ h
    apply Subtype.ext
    apply (selected_type_iff a N φ η j hj e f).mp
    rw [stage_type, stage_type]
    exact congrArg Subtype.val h
  · rintro ⟨p, e, rfl⟩
    refine ⟨⟨(N.pullback (φ.comp η)).pullback e, ⟨e, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (stage_type a N φ η e).symm

theorem selected_palette_card (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) (j : J) (hj : 0 < n j) :
    (palette (a j) K (stage a N φ η)).ncard =
      (palette (a j) K (N.pullback (φ.comp η))).ncard :=
  (Nat.card_congr (Equiv.ofBijective (selectedPaletteMap a N φ η j)
    (selectedPaletteMap_bijective a N φ η j hj))).symm

theorem selected_palette_finite (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) (j : J) (hj : 0 < n j)
    (hf : (palette (a j) K (N.pullback (φ.comp η))).Finite) :
    (palette (a j) K (stage a N φ η)).Finite := by
  letI := hf.to_subtype
  letI := Finite.of_surjective (selectedPaletteMap a N φ η j)
    (selectedPaletteMap_bijective a N φ η j hj).2
  exact Set.toFinite _

theorem selected_unavoidable_full (a : ∀ j, RelStructure L (Fin (n j)))
    {K : RelStructure L X} {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (η : RelEmbedding K K) (j : J) (hj : 0 < n j)
    (hu : Unavoidable (a j) K (stage a N φ η)) :
    Unavoidable (a j) K (N.pullback (φ.comp η)) := by
  intro α
  apply Set.Subset.antisymm (palette_pullback_subset _ _ _ α)
  rintro p ⟨e, rfl⟩
  have hp : (stage a N φ η).pullback e ∈
      palette (a j) K ((stage a N φ η).pullback α) := by
    rw [hu α]
    exact ⟨e, rfl⟩
  obtain ⟨v, hv⟩ := hp
  refine ⟨v, ?_⟩
  change (stage a N φ η).pullback (α.comp v) = (stage a N φ η).pullback e at hv
  exact (selected_type_iff a N φ η j hj (α.comp v) e).mp hv

/-- Full-table preservation upgrades to an actual embedding of the
finite naming expansion.  This direction needs no nullary restriction. -/
theorem family_preservation_embedding (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y₀ Z : RelStructure S X) (g : RelEmbedding K K)
    (h : PreservesFamily a K Z g) :
    IsEmbeddingMap (onStructure a K Y₀ K Z) (onStructure a K Y₀ K Z) g := by
  refine ⟨g.injective, ?_⟩
  intro r R t
  cases R with
  | inl R => exact g.map_rel R t
  | inr R =>
    rcases R with ⟨j, q⟩
    let u := t ∘ Fin.cast j.property.1
    have hinj : Function.Injective (g ∘ u) ↔ Function.Injective u := g.injective.of_comp_iff u
    have hb : K.pullback (g ∘ u) = K.pullback u := by
      change (K.pullback g).pullback u = K.pullback u
      rw [g.pullback_eq]
    change (Function.Injective u ∧ K.pullback u = a j.val ∧ Z.pullback u = q.val) ↔
      (Function.Injective (g ∘ u) ∧ K.pullback (g ∘ u) = a j.val ∧
        Z.pullback (g ∘ u) = q.val)
    rw [hinj, hb]
    by_cases hi : Function.Injective u
    · by_cases hk : K.pullback u = a j.val
      · let e : RelEmbedding (a j.val) K := {
          toFun := u
          injective := hi
          map_rel := fun R t =>
            (congrArg (fun Q => Q.rel R t) hk).symm.to_iff }
        have he := h j.val e
        change Z.pullback (g ∘ u) = Z.pullback u at he
        rw [he]
      · simp only [hk, false_and, and_false]
    · simp only [hi, false_and]

/-- The upper-bound assertion in the finite-stage lemma does not use
unavoidability. Names are fixed by the initial source palette. -/
theorem degree_upper (a : ∀ j, RelStructure L (Fin (n j)))
    (ι : LanguageInclusion L S)
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) (φ : RelEmbedding K B) (θ : RelEmbedding B K)
    (η : RelEmbedding K K) (j : J) (hj : 0 < n j)
    (ha : Nonempty (RelEmbedding (a j) K))
    (hf : (palette (a j) K (N.pullback (φ.comp η))).Finite)
    (hR : ∀ p ∈ palette (a j) K (N.pullback (φ.comp η)), SourceDegreeOne N p) :
    EmbeddingDegreeBound (a j) K (palette (a j) K (stage a N φ η)).ncard := by
  rw [selected_palette_card a N φ η j hj]
  exact source_degree_bound ι hN (embedding_approximate θ) (φ.comp η) ha hf hR

/-- The complete generalized finite-stage lemma, including the empty
selected family. All finite-stage palettes are exact and the actual
finite naming expansion is recurrent on the original carrier. -/
theorem finite_stage [Fintype J]
    (a : ∀ j, RelStructure L (Fin (n j))) (hpos : ∀ j, 0 < n j)
    (ι : LanguageInclusion L S)
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) (φ : RelEmbedding K B) (θ : RelEmbedding B K)
    (η : RelEmbedding K K)
    (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hf : ∀ j, (palette (a j) K (N.pullback (φ.comp η))).Finite)
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback (φ.comp η)) → SourceDegreeOne N p)
    (hu : ∀ j, Unavoidable (a j) K (stage a N φ η)) :
    (∀ j, ExactEmbeddingDegree (a j) K (palette (a j) K (stage a N φ η)).ncard) ∧
      ∀ g : RelEmbedding K K, ∃ h : RelEmbedding K K,
        IsEmbeddingMap (stage a N φ η) (stage a N φ η) (g.comp h) := by
  classical
  have hfull : ∀ j, Unavoidable (a j) K (N.pullback (φ.comp η)) :=
    fun j => selected_unavoidable_full a N φ η j (hpos j) (hu j)
  constructor
  · intro j
    refine ⟨degree_upper a ι hN φ θ η j (hpos j) (ha j) (hf j) (hR j), ?_⟩
    intro t ht
    have hstagefin := selected_palette_finite a N φ η j (hpos j) (hf j)
    letI := hstagefin.fintype
    have hh := RamseyCommon.Palette.unavoidable_degree_lowerBound
      (fun (g : RelEmbedding K K) (e : RelEmbedding (a j) K) => g.comp e)
      (fun e => (⟨(stage a N φ η).pullback e, ⟨e, rfl⟩⟩ :
        palette (a j) K (stage a N φ η)))
      (type_coloring_surjective (stage a N φ η) (hu j)) ht
    simpa only [Set.fintypeCard_eq_ncard] using hh
  · intro g
    obtain ⟨h, hh⟩ := coarse_recurrence ι a hN (embedding_approximate θ)
      (φ.comp η) ha hf hfull hR g
    refine ⟨h, ?_⟩
    rw [stage_eq]
    exact family_preservation_embedding a K (N.pullback φ)
      (N.pullback (φ.comp η)) (g.comp h) hh

end CombinedRamsey.Revised20261018.FiniteStage
