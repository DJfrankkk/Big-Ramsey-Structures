import CombinedRamsey.Negative.ConstrainedExtension
import CombinedRamsey.Negative.EncodingAgeOrder
import CombinedRamsey.Negative.EncodingFreeAmalgamation
import CombinedRamsey.Negative.PersistenceLinkedAmalgam
import Mathlib.Logic.Denumerable

/-! The concrete countably infinite constrained generic and all its actual APIs. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

def constrainedForward {X Y : Type} (K : RelStructure language X) (e : X ≃ Y) :
    RelEmbedding K (K.pullback e.symm) where
  toFun := e
  injective := e.injective
  map_rel R t := by
    change K.rel R t ↔ K.rel R (e.symm ∘ e ∘ t)
    simp [Function.comp_def]

theorem constrained_EP_domainEquiv {X Y : Type} (K : RelStructure language X)
    (hEP : ConstrainedGeneric.ExtensionProperty language LegalModel K) (e : X ≃ Y) :
    ConstrainedGeneric.ExtensionProperty language LegalModel (K.pullback e.symm) := by
  intro n B hB f
  let back := RelEmbedding.pullback K e.symm e.symm.injective
  obtain ⟨g,hg⟩ := hEP n B hB (back.comp f)
  refine ⟨(constrainedForward K e).comp g,?_⟩
  intro i
  change e (g i.castSucc) = f i
  rw [hg]
  exact e.apply_symm_apply (f i)

namespace ConcreteGeneric

abbrev Domain := ConstrainedGeneric.Limit language LegalModel language_finite legalRules

noncomputable def model : RelStructure language Domain :=
  ConstrainedGeneric.limitModel language LegalModel language_finite legalRules

theorem model_legal : LegalModel model :=
  ConstrainedGeneric.limit_legal language LegalModel language_finite legalRules

theorem model_EP : ConstrainedGeneric.ExtensionProperty language LegalModel model :=
  ConstrainedGeneric.extension_property language LegalModel language_finite legalRules

instance domain_countable : Countable Domain :=
  ConstrainedGeneric.countable_limit language LegalModel language_finite legalRules

instance domain_infinite : Infinite Domain :=
  ConstrainedGeneric.infinite_limit language LegalModel language_finite legalRules

noncomputable def enumNat : Domain ≃ ℕ :=
  Classical.choice (inferInstance : Nonempty (Domain ≃ ℕ))

noncomputable def natModel : RelStructure language ℕ := model.pullback enumNat.symm

theorem natModel_legal : LegalModel natModel :=
  legalModel_hereditary model model_legal enumNat.symm enumNat.symm.injective

theorem natModel_injective : natModel.InjectiveRelations := natModel_legal.1

theorem natModel_EP : ConstrainedGeneric.ExtensionProperty language LegalModel natModel :=
  constrained_EP_domainEquiv model model_EP enumNat

theorem natModel_rel_finite_extension : RelFiniteExtension natModel :=
  constrained_rel_finite_extension natModel natModel_EP

theorem natModel_ultrahomogeneous :
    @FirstOrder.Language.IsUltrahomogeneous language.toFirstOrder ℕ natModel.toFirstOrder :=
  constrained_ultrahomogeneous natModel natModel_legal natModel_EP

theorem natModel_finite_homogeneous : FiniteEmbeddingHomogeneous natModel :=
  constrained_finite_homogeneous natModel natModel_legal natModel_EP

theorem natModel_age_exact {V : Type} [Finite V] (A : RelStructure language V) :
    Nonempty (RelEmbedding A natModel) ↔ LegalModel A :=
  constrained_age_exact natModel natModel_legal natModel_EP A

theorem natModel_age_shared_free : AgeSharedFree natModel := by
  intro B Y Z _ _ _ ML MR hbase hL hR
  apply (natModel_age_exact _).mpr
  exact legalModel_shared_free_amalgam ML MR
    ((natModel_age_exact ML).mp hL) ((natModel_age_exact MR).mp hR) hbase

theorem boundary_legal_model {k : ℕ} (H : Digraph (Fin k)) : LegalModel (boundary H).toRel :=
  ⟨(boundary H).toRel_injective, (Table.canonical_legal_iff (boundary H)).mpr (boundary_legal H)⟩

noncomputable def baseEmbedding {k : ℕ} (H : Digraph (Fin k)) :
    RelEmbedding (boundary H).toRel natModel :=
  Classical.choice ((natModel_age_exact (boundary H).toRel).mpr (boundary_legal_model H))

theorem encoded_realizations_nonempty {k : ℕ} (H : Digraph (Fin k)) :
    (EncodedRealizations H natModel (baseEmbedding H)).Nonempty := by
  have htype : LegalModel (typeTable H).toRel :=
    ⟨(typeTable H).toRel_injective,
      (Table.canonical_legal_iff (typeTable H)).mpr (typeTable_legal H)⟩
  let old : RelEmbedding ((typeTable H).toRel.pullback Sum.inl) natModel := {
    toFun := baseEmbedding H
    injective := (baseEmbedding H).injective
    map_rel := fun R t =>
      (Iff.of_eq (congrArg (fun D => D.rel R t) (boundary_type_reduct H))).trans
        ((baseEmbedding H).map_rel R t) }
  obtain ⟨g,hg⟩ := constrained_extend_one_point natModel natModel_EP (typeTable H).toRel htype old
  exact ⟨g (.inr ()),g,hg,rfl⟩

theorem labelled_realizations_nonempty {k : ℕ} (H : Digraph (Fin k)) :
    (Realizations (labelledType H) natModel (labelledBase H natModel (baseEmbedding H))).Nonempty := by
  rw [labelled_realizations_eq]
  exact encoded_realizations_nonempty H

theorem actual_age_hom_order {k k' : ℕ} (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k')) :
    (∀ n (a : RelStructure language (Fin n)),
      InAgeOn natModel (EncodedRealizations H natModel (baseEmbedding H)) a →
      InAgeOn natModel (EncodedRealizations H' natModel (baseEmbedding H')) a) ↔
      Nonempty (Hom H H') :=
  encoded_age_hom_order hk hk' H H' natModel natModel_injective natModel_legal.2
    natModel_rel_finite_extension (baseEmbedding H) (baseEmbedding H')

theorem actual_separating_pattern {k k' : ℕ} (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k')) (hno : ¬ Nonempty (Hom H H')) :
    InAgeOn natModel (EncodedRealizations H natModel (baseEmbedding H)) (hubPattern H) ∧
      ¬ InAgeOn natModel (EncodedRealizations H' natModel (baseEmbedding H')) (hubPattern H) :=
  encoded_age_separating_pattern hk hk' H H' natModel natModel_legal.2 natModel_rel_finite_extension
    (baseEmbedding H) (baseEmbedding H') hno

theorem labelled_separating_pattern {k k' : ℕ} (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k')) (hno : ¬ Nonempty (Hom H H')) :
    InAgeOn natModel (Realizations (labelledType H) natModel
      (labelledBase H natModel (baseEmbedding H))) (hubPattern H) ∧
      ¬ InAgeOn natModel (Realizations (labelledType H') natModel
        (labelledBase H' natModel (baseEmbedding H'))) (hubPattern H) := by
  rw [labelled_realizations_eq, labelled_realizations_eq]
  exact actual_separating_pattern hk hk' H H' hno

end ConcreteGeneric

end CombinedRamsey.Negative
