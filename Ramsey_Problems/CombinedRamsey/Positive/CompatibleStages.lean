import CombinedRamsey.Positive.ProfileMain
import CombinedRamsey.Positive.FiniteStage

/-! Literal whole-structure prefix compatibility of the optimal stages.
Stages live on the same original domain; no intersection of self-copy
ranges is used. Only the finite-stage expansions are asserted recurrent. -/

namespace CombinedRamsey.Positive.Relational.Truncation

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding
open RelationalRamsey632.RelStructure RelationalRamsey632.Transfer

variable (L : Language) [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)]

def stepInclusion (n : ℕ) : LanguageInclusion (language L n) (language L (n + 1)) where
  relMap _ R := match R with
    | Sum.inl R => Sum.inl R
    | Sum.inr R => Sum.inr ⟨R.val, Nat.le_succ_of_le R.property⟩
  relInjective r := by
    intro R T h
    cases R with
    | inl R =>
      cases T with
      | inl T => exact congrArg Sum.inl (Sum.inl.inj h)
      | inr T => cases h
    | inr R =>
      cases T with
      | inl T => cases h
      | inr T =>
        apply congrArg Sum.inr
        apply Subtype.ext
        have he : (⟨R.val, Nat.le_succ_of_le R.property⟩ :
          {R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r // r ≤ n + 1}) =
          ⟨T.val, Nat.le_succ_of_le T.property⟩ := Sum.inr.inj h
        exact congrArg (fun s :
          {R : (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r // r ≤ n + 1} => s.val) he

omit [IsEmpty (L.Rel 0)] in
theorem successive_reduct (n : ℕ) (Y : RelStructure (expandedSourceLanguage L) ℕ) :
    (Y.reduct (inclusion L (n + 1))).reduct (stepInclusion L n) =
      Y.reduct (inclusion L n) := by
  apply RelStructure.ext_rel
  intro r R t
  cases R <;> rfl

noncomputable def stage (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (η : ℕ → RelationalRamsey632.RelEmbedding K K) (n : ℕ) :
    RelStructure (language L n) ℕ :=
  pullback L n ((codingEmbedding L K hK).comp (η n))

/-- Full finite-type stabilization yields an equality of entire stage
interpretations with the corresponding prefix of Y, on the fixed domain. -/
theorem stage_eq_limit_reduct (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (η : ℕ → RelationalRamsey632.RelEmbedding K K)
    (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hY : Y.reduct (Relational.baseInclusion L) = K)
    (hs : ∀ m (a : RelStructure L (Fin m))
      (_ha : Nonempty (RelationalRamsey632.RelEmbedding a K)),
      ∀ n, m ≤ n → ∀ e : RelationalRamsey632.RelEmbedding a K,
        Y.pullback e =
          ((expandedSource L).pullback ((codingEmbedding L K hK).comp (η n))).pullback e)
    (n : ℕ) : stage L K hK η n = Y.reduct (inclusion L n) := by
  have hstage : FullStageAgreement L K η Y :=
    fun m a ha e => hs m a ha m le_rfl e
  have hinj := stage_Y_injective L K η Y hstage
  apply RelStructure.ext_rel
  intro r R t
  cases R with
  | inl R =>
    have hy := congrArg (fun a => a.rel R t) hY
    exact ((((codingEmbedding L K hK).comp (η n)).map_rel R t).symm).trans hy.to_iff.symm
  | inr R =>
    by_cases ht : Function.Injective t
    · let a := K.pullback t
      let e : RelationalRamsey632.RelEmbedding a K := RelationalRamsey632.RelEmbedding.pullback K t ht
      have heq := hs r a ⟨e⟩ n R.property e
      have he := congrArg (fun p => p.rel (Sum.inr R.val) (id : Fin r → Fin r)) heq
      exact he.to_iff.symm
    · apply iff_of_false
      · intro h
        have hi : Function.Injective (((codingEmbedding L K hK).comp (η n)) ∘ t) := h.1
        exact ht hi.of_comp
      · intro h
        exact ht (hinj r (Sum.inr R.val) t R.val.property h)

theorem literal_stage_compatibility (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (η : ℕ → RelationalRamsey632.RelEmbedding K K)
    (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (heq : ∀ n, stage L K hK η n = Y.reduct (inclusion L n)) :
    ∀ n, (stage L K hK η (n + 1)).reduct (stepInclusion L n) = stage L K hK η n := by
  intro n
  rw [heq (n + 1), heq n]
  exact successive_reduct L n Y

theorem stage_selected_finite (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (η : ℕ → RelationalRamsey632.RelEmbedding K K) (n : ℕ)
    (j : BoundedPositiveIsoIndex K n) :
    (palette (selectedFamily L K n j) K (stage L K hK η n)).Finite := by
  classical
  have hsource := precompact_source_pullback (uniform_source_conditions L K hK) (η n)
  have hfull := (hsource _ (selectedFamily L K n j) (selected_realized L K n j)).1
  let E := paletteEquiv L n ((codingEmbedding L K hK).comp (η n))
    (selectedFamily L K n j) (selected_size_le L K n j)
  haveI : Finite (palette (selectedFamily L K n j) K
    ((expandedSource L).pullback ((codingEmbedding L K hK).comp (η n)))) := hfull.to_subtype
  haveI : Finite (palette (selectedFamily L K n j) K (stage L K hK η n)) :=
    Finite.of_surjective E E.surjective
  exact Set.toFinite _

theorem stage_selected_unavoidable (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (η : ℕ → RelationalRamsey632.RelEmbedding K K)
    (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (heq : ∀ n, stage L K hK η n = Y.reduct (inclusion L n))
    (hall : OriginalConclusion L K hK Y) (n : ℕ) (j : BoundedPositiveIsoIndex K n) :
    Unavoidable (selectedFamily L K n j) K (stage L K hK η n) := by
  have hu := (hall _ (selectedFamily L K n j) (selected_realized L K n j)).2.1
  rw [heq n]
  intro f
  apply Set.Subset.antisymm (palette_pullback_subset _ _ _ f)
  rintro p ⟨e, rfl⟩
  have hp : Y.pullback e ∈ palette (selectedFamily L K n j) K (Y.pullback f) :=
    (hu f).symm ▸ ⟨e, rfl⟩
  obtain ⟨g, hg⟩ := hp
  exact ⟨g, congrArg (fun a => a.reduct (inclusion L n)) hg⟩

/-- One optimal system has literal prefix identities and every F_n is
recurrent with exact selected palettes. Recurrence of the union is not claimed. -/
theorem compatible_recurrent_optimal_system (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) :
    ∃ η : ℕ → RelationalRamsey632.RelEmbedding K K,
      ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
        Y.reduct (Relational.baseInclusion L) = K ∧
        η 0 = RelationalRamsey632.RelEmbedding.refl K ∧
        (∀ n, ∃ u : RelationalRamsey632.RelEmbedding K K, η (n + 1) = (η n).comp u) ∧
        OriginalConclusion L K hK Y ∧
        ActiveConclusion L K Y ∧
        (∀ n, stage L K hK η n = Y.reduct (inclusion L n)) ∧
        (∀ n, (stage L K hK η (n + 1)).reduct (stepInclusion L n) = stage L K hK η n) ∧
        ∀ n,
          (∀ j : BoundedPositiveIsoIndex K n,
            ExactEmbeddingDegree (selectedFamily L K n j) K
              (palette (selectedFamily L K n j) K (stage L K hK η n)).ncard) ∧
          (∀ g : RelationalRamsey632.RelEmbedding K K,
            ∃ h : RelationalRamsey632.RelEmbedding K K,
              IsEmbeddingMap (stage L K hK η n) (stage L K hK η n) (g.comp h)) := by
  obtain ⟨η, Y, hY, hzero, hnested, hs, hall, _⟩ := size_indexed_optimal_system L K hK hEP
  have heq : ∀ n, stage L K hK η n = Y.reduct (inclusion L n) :=
    stage_eq_limit_reduct L K hK η Y hY hs
  have hstage : FullStageAgreement L K η Y := fun m a ha e => hs m a ha m le_rfl e
  have hactive := active_conclusion L K hK η Y hstage hY hall
  refine ⟨η, Y, hY, hzero, hnested, hall, hactive, heq, literal_stage_compatibility L K hK η Y heq, ?_⟩
  intro n
  exact finite_stage_lemma L K hK hEP n ((codingEmbedding L K hK).comp (η n))
    (stage_selected_finite L K hK η n) (stage_selected_unavoidable L K hK η Y heq hall n)

end CombinedRamsey.Positive.Relational.Truncation
