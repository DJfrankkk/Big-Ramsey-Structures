import CombinedRamsey.Positive.ProfileOptimal

/-! Literal N≤n: the whole base language is kept, and precisely the NF
predicates of arity at most n are retained. Full source tables on a finite
domain of size at most n are uniquely determined by this reduct. -/

namespace CombinedRamsey.Positive.Relational.Truncation

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding
open RelationalRamsey632.RelStructure RelationalRamsey632.Transfer

variable (L : Language) [∀ r, Fintype (L.Rel r)]

def language (n : ℕ) : Language where
  Rel r := L.Rel r ⊕ {_R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r // r ≤ n}

def inclusion (n : ℕ) : LanguageInclusion (language L n) (expandedSourceLanguage L) where
  relMap _ R := match R with
    | Sum.inl R => Sum.inl R
    | Sum.inr R => Sum.inr R.val
  relInjective _ := by
    intro R T h
    cases R <;> cases T
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

def baseInclusion (n : ℕ) : LanguageInclusion L (language L n) where
  relMap _ := Sum.inl
  relInjective _ := Sum.inl_injective

noncomputable def source (n : ℕ) : RelStructure (language L n) (DecoderVertex L) :=
  (expandedSource L).reduct (inclusion L n)

noncomputable def pullback (n : ℕ) {K : RelStructure L ℕ}
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) : RelStructure (language L n) ℕ :=
  (source L n).pullback ξ

theorem pullback_reduct (n : ℕ) {K : RelStructure L ℕ}
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) :
    (pullback L n ξ).reduct (baseInclusion L n) = K := ξ.pullback_eq

theorem above_bound_false {F : Type} [Finite F] {n r : ℕ} (hF : Nat.card F ≤ n)
    (hr : n < r) (R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r)
    (f : F → DecoderVertex L) (t : Fin r → F) :
    ¬ (expandedSource L).rel (Sum.inr R) (f ∘ t) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  intro h
  have hi : Function.Injective t := h.1.of_comp
  have hcard := Fintype.card_le_of_injective t hi
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hcard
  omega

theorem full_table_eq_of_trunc_eq {F : Type} [Finite F] {n : ℕ}
    (hF : Nat.card F ≤ n) (f g : F → DecoderVertex L)
    (heq : (source L n).pullback f = (source L n).pullback g) :
    (expandedSource L).pullback f = (expandedSource L).pullback g := by
  apply RelStructure.ext_rel
  intro r R t
  cases R with
  | inl R => exact (congrArg (fun a => a.rel (Sum.inl R) t) heq).to_iff
  | inr R =>
    by_cases hr : r ≤ n
    · exact (congrArg (fun a => a.rel (Sum.inr ⟨R, hr⟩) t) heq).to_iff
    · exact iff_of_false (above_bound_false L hF (by omega) R f t)
        (above_bound_false L hF (by omega) R g t)

def paletteMap {F : Type} {K : RelStructure L ℕ} (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F) :
    palette a K ((expandedSource L).pullback ξ) → palette a K (pullback L n ξ) := fun p =>
  ⟨p.val.reduct (inclusion L n), by
    obtain ⟨e, he⟩ := p.property
    exact ⟨e, congrArg (fun z => z.reduct (inclusion L n)) he⟩⟩

theorem paletteMap_bijective {F : Type} [Finite F] {K : RelStructure L ℕ} (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F)
    (hF : Nat.card F ≤ n) : Function.Bijective (paletteMap L n ξ a) := by
  constructor
  · intro p q h
    apply Subtype.ext
    obtain ⟨e, he⟩ := p.property
    obtain ⟨f, hf⟩ := q.property
    have hr := congrArg (fun z => z.val) h
    change p.val.reduct (inclusion L n) = q.val.reduct (inclusion L n) at hr
    rw [← he, ← hf] at hr
    rw [← he, ← hf]
    exact full_table_eq_of_trunc_eq L hF (ξ ∘ e) (ξ ∘ f) hr
  · rintro ⟨p, e, rfl⟩
    exact ⟨⟨((expandedSource L).pullback ξ).pullback e, ⟨e, rfl⟩⟩, rfl⟩

noncomputable def paletteEquiv {F : Type} [Finite F] {K : RelStructure L ℕ} (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F)
    (hF : Nat.card F ≤ n) :
    palette a K ((expandedSource L).pullback ξ) ≃ palette a K (pullback L n ξ) :=
  Equiv.ofBijective (paletteMap L n ξ a) (paletteMap_bijective L n ξ a hF)

theorem full_palette_finite {F : Type} [Finite F] {K : RelStructure L ℕ} (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F)
    (hF : Nat.card F ≤ n) (hfin : (palette a K (pullback L n ξ)).Finite) :
    (palette a K ((expandedSource L).pullback ξ)).Finite := by
  haveI : Finite (palette a K (pullback L n ξ)) := hfin.to_subtype
  haveI : Finite (palette a K ((expandedSource L).pullback ξ)) :=
    Finite.of_equiv _ (paletteEquiv L n ξ a hF).symm
  exact Set.toFinite _

theorem palette_card_eq {F : Type} [Finite F] {K : RelStructure L ℕ} (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F)
    (hF : Nat.card F ≤ n) :
    (palette a K ((expandedSource L).pullback ξ)).ncard =
      (palette a K (pullback L n ξ)).ncard := Nat.card_congr (paletteEquiv L n ξ a hF)

theorem full_palette_unavoidable {F : Type} [Finite F] {K : RelStructure L ℕ} (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F)
    (hF : Nat.card F ≤ n) (hu : Unavoidable a K (pullback L n ξ)) :
    Unavoidable a K ((expandedSource L).pullback ξ) := by
  intro α
  apply Set.Subset.antisymm (palette_pullback_subset a K _ α)
  rintro p ⟨e, rfl⟩
  have hp : (pullback L n ξ).pullback e ∈ palette a K ((pullback L n ξ).pullback α) :=
    (hu α).symm ▸ ⟨e, rfl⟩
  obtain ⟨f, hf⟩ := hp
  exact ⟨f, full_table_eq_of_trunc_eq L hF (ξ ∘ α ∘ f) (ξ ∘ e) hf⟩

theorem source_ramsey_for_palette {F : Type} [Finite F] {K : RelStructure L ℕ}
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L)) (a : RelStructure L F) :
    ∀ p ∈ palette a K ((expandedSource L).pullback ξ), SourceDegreeOne (expandedSource L) p := by
  intro p hp
  obtain ⟨e, he⟩ := hp
  have f := RelationalRamsey632.RelEmbedding.pullback (expandedSource L) (ξ.comp e) (ξ.comp e).injective
  change RelationalRamsey632.RelEmbedding ((expandedSource L).pullback (ξ.comp e)) (expandedSource L) at f
  change (expandedSource L).pullback (ξ.comp e) = p at he
  rw [he] at f
  exact source_degree_one_lift L p f
    (sourceDegreeOne (p.reduct (nfInclusion L)) ⟨nfReductEmbedding L f⟩)

end CombinedRamsey.Positive.Relational.Truncation
