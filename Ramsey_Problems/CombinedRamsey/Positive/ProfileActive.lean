import CombinedRamsey.Positive.ProfileStableSystem
import Mathlib.Data.Finite.Sum

/-! Delete exactly the unused initial NF names from the stabilized expansion. -/

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.RelStructure
open RelationalRamsey632.Coding RelationalRamsey632.Transfer

variable (L : Language) [∀ r, Fintype (L.Rel r)]

def FullStageAgreement (K : RelStructure L ℕ) (eta : ℕ → RelationalRamsey632.RelEmbedding K K)
    (Y : RelStructure (expandedSourceLanguage L) ℕ) : Prop :=
  ∀ m (b : RelStructure L (Fin m)) (_hb : Nonempty (RelationalRamsey632.RelEmbedding b K))
    (e : RelationalRamsey632.RelEmbedding b K),
    Y.pullback e = ((expandedSource L).pullback (codingMap L K ∘ eta m)).pullback e

theorem every_tuple_agrees_with_stage (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) {r : ℕ} (t : Fin r → ℕ) :
    ∃ m, ∀ R : (expandedSourceLanguage L).Rel r,
      Y.rel R t ↔ (expandedSource L).rel R (codingMap L K ∘ eta m ∘ t) := by
  classical
  let m := Finset.univ.sup t + 1
  let q : Fin r → Fin m := fun j => ⟨t j, by
    have h := Finset.le_sup (f := t) (Finset.mem_univ j)
    omega⟩
  let b := K.pullback (Fin.val : Fin m → ℕ)
  let e : RelationalRamsey632.RelEmbedding b K :=
    RelationalRamsey632.RelEmbedding.pullback K Fin.val Fin.val_injective
  have hs := hstage m b ⟨e⟩ e
  refine ⟨m, ?_⟩
  intro R
  have h := congrArg (fun p : RelStructure (expandedSourceLanguage L) (Fin m) => p.rel R q) hs
  exact h.to_iff

theorem stage_inactive_false (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) {r : ℕ}
    (R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r)
    (h : R.val ∉ codingNormalForms L K r) (t : Fin r → ℕ) : ¬ Y.rel (Sum.inr R) t := by
  intro ht
  obtain ⟨m, hm⟩ := every_tuple_agrees_with_stage L K eta Y hstage t
  have hs := (hm (Sum.inr R)).mp ht
  change Function.Injective (codingMap L K ∘ eta m ∘ t) ∧
    normalForm (codingMap L K ∘ eta m ∘ t) = R.val at hs
  let u : Fin r ↪ ℕ := ⟨eta m ∘ t, hs.1.of_comp⟩
  exact h ⟨u, hs.2⟩

theorem stage_Y_injective (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) : Y.InjectiveRelations := by
  intro r R t hr ht
  obtain ⟨m, hm⟩ := every_tuple_agrees_with_stage L K eta Y hstage t
  have hs := (hm R).mp ht
  cases R with
  | inl R => exact (decoder_injective L r R _ hr hs).of_comp.of_comp
  | inr R => exact hs.1.of_comp.of_comp

def activeLanguage (K : RelStructure L ℕ) : Language where
  Rel r := L.Rel r ⊕
    {R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r //
      R.val ∈ codingNormalForms L K r}

def activeInclusion (K : RelStructure L ℕ) :
    LanguageInclusion (activeLanguage L K) (expandedSourceLanguage L) where
  relMap _ R := match R with
    | Sum.inl R => Sum.inl R
    | Sum.inr R => Sum.inr R.val
  relInjective _ := by
    intro R T h
    cases R with
    | inl R =>
      cases T with
      | inl T => exact congrArg Sum.inl (Sum.inl.inj h)
      | inr T => cases h
    | inr R =>
      cases T with
      | inl T => cases h
      | inr T => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

noncomputable def activeStructure (K : RelStructure L ℕ)
    (Y : RelStructure (expandedSourceLanguage L) ℕ) : RelStructure (activeLanguage L K) ℕ :=
  Y.reduct (activeInclusion L K)

theorem active_finite_per_arity (K : RelStructure L ℕ) : (activeLanguage L K).FinitePerArity := by
  intro r
  haveI : Finite (L.Rel r) := inferInstance
  haveI : Finite (codingNormalForms L K r) := (uniform_finite_normal_forms L K r).to_subtype
  haveI : Finite {R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r //
      R.val ∈ codingNormalForms L K r} :=
    Finite.of_injective (fun R => (⟨R.val.val, R.property⟩ : codingNormalForms L K r)) (by
      intro R T h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : codingNormalForms L K r => z.val) h)
  change Finite (L.Rel r ⊕ _)
  infer_instance

theorem active_self_embeddings (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) (f : ℕ → ℕ) :
    IsEmbeddingMap (activeStructure L K Y) (activeStructure L K Y) f ↔ IsEmbeddingMap Y Y f := by
  classical
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨hi, ?_⟩
    intro r R t
    cases R with
    | inl R => exact hm r (Sum.inl R) t
    | inr R =>
      by_cases hR : R.val ∈ codingNormalForms L K r
      · exact hm r (Sum.inr ⟨R, hR⟩) t
      · exact iff_of_false (stage_inactive_false L K eta Y hstage R hR t)
          (stage_inactive_false L K eta Y hstage R hR (f ∘ t))
  · rintro ⟨hi, hm⟩
    exact ⟨hi, fun r R t => hm r ((activeInclusion L K).relMap r R) t⟩

def activePaletteMap (K : RelStructure L ℕ) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    {F : Type} (b : RelStructure L F) :
    palette b K Y → palette b K (activeStructure L K Y) := fun p =>
  ⟨p.val.reduct (activeInclusion L K), by
    obtain ⟨e, he⟩ := p.property
    exact ⟨e, congrArg (fun z => z.reduct (activeInclusion L K)) he⟩⟩

theorem activePaletteMap_bijective (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) {F : Type} (b : RelStructure L F) :
    Function.Bijective (activePaletteMap L K Y b) := by
  classical
  constructor
  · intro p q h
    apply Subtype.ext
    apply RelStructure.ext_rel
    intro r R t
    cases R with
    | inl R =>
      exact (congrArg (fun z : palette b K (activeStructure L K Y) => z.val.rel (Sum.inl R) t) h).to_iff
    | inr R =>
      by_cases hR : R.val ∈ codingNormalForms L K r
      · exact (congrArg (fun z : palette b K (activeStructure L K Y) =>
          z.val.rel (Sum.inr ⟨R, hR⟩) t) h).to_iff
      · obtain ⟨e, he⟩ := p.property
        obtain ⟨f, hf⟩ := q.property
        rw [← he, ← hf]
        exact iff_of_false (stage_inactive_false L K eta Y hstage R hR (e ∘ t))
          (stage_inactive_false L K eta Y hstage R hR (f ∘ t))
  · rintro ⟨p, e, rfl⟩
    exact ⟨⟨Y.pullback e, ⟨e, rfl⟩⟩, rfl⟩

noncomputable def activePaletteEquiv (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) {F : Type} (b : RelStructure L F) :
    palette b K Y ≃ palette b K (activeStructure L K Y) :=
  Equiv.ofBijective (activePaletteMap L K Y b) (activePaletteMap_bijective L K eta Y hstage b)

end CombinedRamsey.Positive.Relational
