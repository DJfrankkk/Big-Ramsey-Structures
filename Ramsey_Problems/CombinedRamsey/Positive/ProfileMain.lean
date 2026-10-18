import CombinedRamsey.Positive.ProfileActive
import RelationalRamsey632.Existence.NatPresentation

/-! The literal finite-per-arity NF expansion and all terminal positive degree conclusions. -/

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.RelStructure
open RelationalRamsey632.Coding RelationalRamsey632.Transfer

variable (L : Language) [∀ r, Fintype (L.Rel r)]

def activeBaseInclusion (K : RelStructure L ℕ) : LanguageInclusion L (activeLanguage L K) where
  relMap _ := Sum.inl
  relInjective _ := Sum.inl_injective

theorem active_expands (K : RelStructure L ℕ) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hY : Y.reduct (baseInclusion L) = K) :
    (activeStructure L K Y).reduct (activeBaseInclusion L K) = K := hY

theorem active_injective (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) : (activeStructure L K Y).InjectiveRelations := by
  intro r R t hr ht
  exact stage_Y_injective L K eta Y hstage r ((activeInclusion L K).relMap r R) t hr ht

theorem active_palette_unavoidable (K : RelStructure L ℕ)
    (Y : RelStructure (expandedSourceLanguage L) ℕ) {F : Type} (b : RelStructure L F)
    (hu : Unavoidable b K Y) : Unavoidable b K (activeStructure L K Y) := by
  intro alpha
  apply Set.Subset.antisymm (palette_pullback_subset _ _ _ alpha)
  rintro p ⟨e, rfl⟩
  have hmember : Y.pullback e ∈ palette b K (Y.pullback alpha) := (hu alpha).symm ▸ ⟨e, rfl⟩
  obtain ⟨f, hf⟩ := hmember
  exact ⟨f, congrArg (fun z => z.reduct (activeInclusion L K)) hf⟩

theorem active_palette_rigid (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) {F : Type} (b : RelStructure L F)
    (hRigid : ∀ p ∈ palette b K Y, Rigid p) :
    ∀ p ∈ palette b K (activeStructure L K Y), Rigid p := by
  classical
  rintro p ⟨e, rfl⟩ sigma hsigma
  apply hRigid (Y.pullback e) ⟨e, rfl⟩ sigma
  apply RelStructure.ext_rel
  intro r R t
  cases R with
  | inl R =>
    exact (congrArg (fun z : RelStructure (activeLanguage L K) F => z.rel (Sum.inl R) t) hsigma).to_iff
  | inr R =>
    by_cases hR : R.val ∈ codingNormalForms L K r
    · exact (congrArg (fun z : RelStructure (activeLanguage L K) F =>
        z.rel (Sum.inr ⟨R, hR⟩) t) hsigma).to_iff
    · exact iff_of_false (stage_inactive_false L K eta Y hstage R hR (e ∘ sigma ∘ t))
        (stage_inactive_false L K eta Y hstage R hR (e ∘ t))

theorem active_palette_canonical (K : RelStructure L ℕ)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) {F D : Type} [Fintype D]
    (b : RelStructure L F) (c : RelationalRamsey632.RelEmbedding b K → D)
    (hcanon : ∃ g : RelationalRamsey632.RelEmbedding K K, ∃ d : palette b K Y → D,
      ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩) :
    ∃ g : RelationalRamsey632.RelEmbedding K K,
      ∃ d : palette b K (activeStructure L K Y) → D,
        ∀ e, c (g.comp e) = d ⟨(activeStructure L K Y).pullback e, ⟨e, rfl⟩⟩ := by
  let E := activePaletteEquiv L K eta Y hstage b
  obtain ⟨g, d, hd⟩ := hcanon
  refine ⟨g, d ∘ E.symm, ?_⟩
  intro e
  rw [hd e]
  exact congrArg d (E.symm_apply_apply ⟨Y.pullback e, ⟨e, rfl⟩⟩).symm

def ActiveConclusion (K : RelStructure L ℕ)
    (Y : RelStructure (expandedSourceLanguage L) ℕ) : Prop :=
  (activeLanguage L K).FinitePerArity ∧
    (activeStructure L K Y).reduct (activeBaseInclusion L K) = K ∧
    (activeStructure L K Y).InjectiveRelations ∧
    ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (_hb : Nonempty (RelationalRamsey632.RelEmbedding b K)),
      (palette b K (activeStructure L K Y)).Finite ∧
      Unavoidable b K (activeStructure L K Y) ∧
      ExactEmbeddingDegree b K (palette b K (activeStructure L K Y)).ncard ∧
      ExactCopyDegree b K ((palette b K (activeStructure L K Y)).ncard / Nat.card (automorphismGroup b)) ∧
      (∀ p ∈ palette b K (activeStructure L K Y), Rigid p) ∧
      ∀ (D : Type) [Fintype D] (c : RelationalRamsey632.RelEmbedding b K → D),
        ∃ g : RelationalRamsey632.RelEmbedding K K,
          ∃ d : palette b K (activeStructure L K Y) → D,
            ∀ e, c (g.comp e) = d ⟨(activeStructure L K Y).pullback e, ⟨e, rfl⟩⟩

variable [IsEmpty (L.Rel 0)]

theorem active_conclusion (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (eta : ℕ → RelationalRamsey632.RelEmbedding K K) (Y : RelStructure (expandedSourceLanguage L) ℕ)
    (hstage : FullStageAgreement L K eta Y) (hY : Y.reduct (baseInclusion L) = K)
    (hall : OriginalConclusion L K hK Y) : ActiveConclusion L K Y := by
  classical
  refine ⟨active_finite_per_arity L K, active_expands L K Y hY, active_injective L K eta Y hstage, ?_⟩
  intro F _ b hb
  obtain ⟨hfin, hu, he, _, _, _, _, hr, hc⟩ := hall F b hb
  let E := activePaletteEquiv L K eta Y hstage b
  haveI : Finite (palette b K Y) := hfin.to_subtype
  haveI : Finite (palette b K (activeStructure L K Y)) := Finite.of_surjective E E.surjective
  have hfinZ : (palette b K (activeStructure L K Y)).Finite := Set.toFinite _
  have hcard : (palette b K Y).ncard = (palette b K (activeStructure L K Y)).ncard := Nat.card_congr E
  have huZ := active_palette_unavoidable L K Y b hu
  have hrZ := active_palette_rigid L K eta Y hstage b hr
  have hcZ : ∀ (D : Type) [Fintype D] (c : RelationalRamsey632.RelEmbedding b K → D),
      ∃ g : RelationalRamsey632.RelEmbedding K K,
        ∃ d : palette b K (activeStructure L K Y) → D,
          ∀ e, c (g.comp e) = d ⟨(activeStructure L K Y).pullback e, ⟨e, rfl⟩⟩ :=
    fun D _ c => active_palette_canonical L K eta Y hstage b c (hc D c)
  obtain ⟨hcopy, hdiv⟩ := exact_copy_degree (activeStructure L K Y) hfinZ huZ hrZ hcZ
  exact ⟨hfinZ, huZ, hcard ▸ he, hdiv ▸ hcopy, hrZ, hcZ⟩

/-- The main positive theorem with exactly the new NF names, finitely many
at each arity, and the same original-alphabet construction used by chi_A. -/
theorem main_unrestricted_theorem (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) :
    ∃ eta : ℕ → RelationalRamsey632.RelEmbedding K K,
      ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
        FullStageAgreement L K eta Y ∧ OriginalConclusion L K hK Y ∧ ActiveConclusion L K Y := by
  obtain ⟨eta, Y, hY, _, _, hs, hall, _⟩ := size_indexed_optimal_system L K hK hEP
  have hstage : FullStageAgreement L K eta Y := fun m b hb e => hs m b hb m le_rfl e
  exact ⟨eta, Y, hstage, hall, active_conclusion L K hK eta Y hstage hY hall⟩

theorem main_generic_theorem :
    let hL : L.FinitePerArity := fun _ => inferInstance
    let K := Existence.GenericConstruction.natModel L hL (fun _ => False)
    let hK := Existence.GenericConstruction.natModel_injective L hL (fun _ => False)
    ∃ eta : ℕ → RelationalRamsey632.RelEmbedding K K,
      ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
        FullStageAgreement L K eta Y ∧ OriginalConclusion L K hK Y ∧ ActiveConclusion L K Y := by
  exact main_unrestricted_theorem L _
    (Existence.GenericConstruction.natModel_injective L _ (fun _ => False))
    (Existence.GenericConstruction.natModel_EP L _ (fun _ => False))

omit [∀ r, Fintype (L.Rel r)] in
theorem main_generic_finite_per_arity (hL : L.FinitePerArity) :
    letI : ∀ r, Finite (L.Rel r) := hL
    letI : ∀ r, Fintype (L.Rel r) := fun r => Fintype.ofFinite (L.Rel r)
    let K := Existence.GenericConstruction.natModel L hL (fun _ => False)
    let hK := Existence.GenericConstruction.natModel_injective L hL (fun _ => False)
    ∃ eta : ℕ → RelationalRamsey632.RelEmbedding K K,
      ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
        FullStageAgreement L K eta Y ∧ OriginalConclusion L K hK Y ∧ ActiveConclusion L K Y := by
  letI : ∀ r, Finite (L.Rel r) := hL
  letI : ∀ r, Fintype (L.Rel r) := fun r => Fintype.ofFinite (L.Rel r)
  exact main_unrestricted_theorem L _
    (Existence.GenericConstruction.natModel_injective L hL (fun _ => False))
    (Existence.GenericConstruction.natModel_EP L hL (fun _ => False))

end CombinedRamsey.Positive.Relational
