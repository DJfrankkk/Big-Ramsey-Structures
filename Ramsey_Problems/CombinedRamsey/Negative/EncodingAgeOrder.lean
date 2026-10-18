import CombinedRamsey.Negative.EncodingLabelledTypes

/-! Finite actual age witnesses, not merely an abstract graph-order reduction. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {X : Type} {k k' : ℕ}

noncomputable def hubEnum (k : ℕ) : Fin (Nat.card (Unit ⊕ Fin k)) ≃ (Unit ⊕ Fin k) := by
  classical
  simpa [Nat.card_eq_fintype_card] using (Fintype.equivFin (Unit ⊕ Fin k)).symm

noncomputable def hubPattern (H : Digraph (Fin k)) :
    RelStructure language (Fin (Nat.card (Unit ⊕ Fin k))) :=
  (hubTable H).toRel.pullback (hubEnum k)

theorem encoded_age_separating_pattern (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k'))
    (K : RelStructure language X) (hKlegal : (Table.ofRel K).Legal)
    (hEP : RelFiniteExtension K)
    (b : RelEmbedding (boundary H).toRel K)
    (b' : RelEmbedding (boundary H').toRel K)
    (hno : ¬ Nonempty (Hom H H')) :
    InAgeOn K (EncodedRealizations H K b) (hubPattern H) ∧
      ¬ InAgeOn K (EncodedRealizations H' K b') (hubPattern H) := by
  have hown := realization_age_completion_sufficiency H K b hEP (hubTable H)
    (hubTable_completion hk H)
  constructor
  · obtain ⟨e,he⟩ := hown
    let into := RelEmbedding.pullback (hubTable H).toRel (hubEnum k) (hubEnum k).injective
    exact ⟨e.comp into, fun x => he (hubEnum k x)⟩
  · rintro ⟨e,he⟩
    let inverse : RelEmbedding (hubTable H).toRel (hubPattern H) := {
      toFun := (hubEnum k).symm
      injective := (hubEnum k).symm.injective
      map_rel := fun R t => by
        change (hubTable H).toRel.rel R t ↔
          (hubTable H).toRel.rel R (hubEnum k ∘ (hubEnum k).symm ∘ t)
        simp [Function.comp_def] }
    have hraw : InAgeOn K (EncodedRealizations H' K b') (hubTable H).toRel :=
      ⟨e.comp inverse, fun x => he ((hubEnum k).symm x)⟩
    have hc := realization_age_completion_necessity H' K b' hKlegal
      (hubTable H) (hubTable_canonical H) hraw
    have hh := ((legal_completion_iff hk' H' (hubTable H)).mp hc).2 (.inl ())
    exact hno ⟨(Classical.choice hh).comp (hubHom H)⟩

theorem encoded_age_hom_order (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k'))
    (K : RelStructure language X) (hKinj : K.InjectiveRelations)
    (hKlegal : (Table.ofRel K).Legal) (hEP : RelFiniteExtension K)
    (b : RelEmbedding (boundary H).toRel K)
    (b' : RelEmbedding (boundary H').toRel K) :
    (∀ n (a : RelStructure language (Fin n)),
      InAgeOn K (EncodedRealizations H K b) a →
      InAgeOn K (EncodedRealizations H' K b') a) ↔ Nonempty (Hom H H') := by
  classical
  constructor
  · intro h
    by_contra hn
    have hs := encoded_age_separating_pattern hk hk' H H' K hKlegal hEP b b' hn
    exact hs.2 (h _ _ hs.1)
  · rintro ⟨g⟩ n a ha
    have hainj : a.InjectiveRelations := by
      obtain ⟨e,_⟩ := ha
      rw [← e.pullback_eq]
      exact K.injectiveRelations_pullback hKinj e
    let B := Table.ofRel a
    have he : B.toRel = a := Table.toRel_ofRel a hainj
    have hc := realization_age_completion_necessity H K b hKlegal B
      (Table.ofRel_canonical a hainj) (he.symm ▸ ha)
    have hc' := completion_age_inclusion_of_hom hk hk' H H' g (Fin n) B hc
    have hh := realization_age_completion_sufficiency H' K b' hEP B hc'
    rwa [he] at hh

end CombinedRamsey.Negative
