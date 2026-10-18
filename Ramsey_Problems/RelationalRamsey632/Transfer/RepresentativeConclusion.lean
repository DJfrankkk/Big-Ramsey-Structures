import RelationalRamsey632.Transfer.IsoRepresentatives

namespace RelationalRamsey632.Transfer.Named

open RelStructure

variable {L S : Language} {X : Type}

theorem representative_big_ramsey (ι : LanguageInclusion L S)
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hYK : Y.reduct ι = K) (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (hall : ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (_hb : Nonempty (RelEmbedding b K)),
      (palette b K Y).Finite ∧ Unavoidable b K Y ∧
      ExactEmbeddingDegree b K (palette b K Y).ncard ∧
      (∀ p ∈ palette b K Y, Rigid p) ∧
      ∀ (D : Type) [Fintype D] (c : RelEmbedding b K → D),
        ∃ g : RelEmbedding K K, ∃ d : palette b K Y → D,
          ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩) :
    (representativeExpansion K Y).reduct (inclusion (isoAgeFamily K) K Y) = K ∧
    (language (isoAgeFamily K) K Y).FinitePerArity ∧
    Countable (Sigma (language (isoAgeFamily K) K Y).Rel) ∧
    (∀ f : X → X, IsEmbeddingMap (representativeExpansion K Y) (representativeExpansion K Y) f ↔
      IsEmbeddingMap Y Y f) ∧
    ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (_hb : Nonempty (RelEmbedding b K)),
      (palette b K (representativeExpansion K Y)).Finite ∧
      Unavoidable b K (representativeExpansion K Y) ∧
      ExactEmbeddingDegree b K (palette b K (representativeExpansion K Y)).ncard ∧
      ExactCopyDegree b K ((palette b K (representativeExpansion K Y)).ncard /
        Nat.card (automorphismGroup b)) ∧
      ((palette b K (representativeExpansion K Y)).ncard = (palette b K Y).ncard) ∧
      (∀ p ∈ palette b K (representativeExpansion K Y), Rigid p) ∧
      ∀ (D : Type) [Fintype D] (c : RelEmbedding b K → D),
        ∃ g : RelEmbedding K K, ∃ d : palette b K (representativeExpansion K Y) → D,
          ∀ e, c (g.comp e) = d ⟨(representativeExpansion K Y).pullback e, ⟨e, rfl⟩⟩ := by
  classical
  have hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite :=
    fun F _ b hb => (hall F b hb).1
  have hD := cover_determines (isoAgeFamily K) K Y (iso_age_family_covers K)
  have hC := representative_finite_per_arity K Y hK hL hfin
  haveI : ∀ r, Finite ((language (isoAgeFamily K) K Y).Rel r) := hC
  refine ⟨rfl, hC, inferInstance, representativeEmbedding_iff ι K Y hYK, ?_⟩
  intro F _ b hb
  obtain ⟨hf, hu, he, hr, hc⟩ := hall F b hb
  have hfC := names_finite_palette (isoAgeFamily K) K Y b hf
  have huC := names_unavoidable (isoAgeFamily K) K Y b hu
  have hrC := names_rigid (isoAgeFamily K) K Y hD b hb hr
  have hcC := names_canonization (isoAgeFamily K) K Y hD b hb hc
  have hcard := names_palette_card (isoAgeFamily K) K Y hD b hb
  obtain ⟨hcopy, hdiv⟩ := exact_copy_degree (representativeExpansion K Y) hfC huC hrC hcC
  exact ⟨hfC, huC, hcard ▸ he, hdiv ▸ hcopy, hcard, hrC, hcC⟩

end RelationalRamsey632.Transfer.Named
