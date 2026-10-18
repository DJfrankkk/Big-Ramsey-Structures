import RelationalRamsey632.Transfer.RepresentativeNames

/-! One actual labelled representative per finite base isomorphism class.
The quotient and representative choice are ordinary Lean constructions;
neither a classification oracle nor an effective minimum algorithm is used. -/

namespace RelationalRamsey632.Transfer.Named

open RelStructure

variable {L S : Language} {X : Type}

def ageIso (K : RelStructure L X) (r : ℕ) (b c : AgeStates K r) : Prop :=
  ∃ σ : Equiv.Perm (Fin r), c.val.pullback σ = b.val

def ageSetoid (K : RelStructure L X) (r : ℕ) : Setoid (AgeStates K r) where
  r := ageIso K r
  iseqv := {
    refl := fun b => ⟨Equiv.refl _, rfl⟩
    symm := by
      intro b c h
      obtain ⟨σ, hσ⟩ := h
      refine ⟨σ.symm, ?_⟩
      rw [← hσ, pullback_comp]
      have he : σ ∘ σ.symm = id := funext (σ.apply_symm_apply)
      rw [he, pullback_id]
    trans := by
      intro b c d hbc hcd
      obtain ⟨σ, hσ⟩ := hbc
      obtain ⟨τ, hτ⟩ := hcd
      refine ⟨σ.trans τ, ?_⟩
      change d.val.pullback (τ ∘ σ) = b.val
      rw [← pullback_comp, hτ, hσ] }

def IsoAge (K : RelStructure L X) (r : ℕ) := Quotient (ageSetoid K r)

noncomputable def representative (K : RelStructure L X) (r : ℕ) (q : IsoAge K r) :
    AgeStates K r := q.out

theorem representative_class (K : RelStructure L X) (r : ℕ) (q : IsoAge K r) :
    Quotient.mk (ageSetoid K r) (representative K r q) = q := Quotient.out_eq q

theorem representative_unique (K : RelStructure L X) (r : ℕ) (p q : IsoAge K r) :
    ageIso K r (representative K r p) (representative K r q) ↔ p = q := by
  constructor
  · intro h
    have he : Quotient.mk (ageSetoid K r) (representative K r p) =
        Quotient.mk (ageSetoid K r) (representative K r q) := Quotient.sound h
    rw [representative_class, representative_class] at he
    exact he
  · intro h
    subst q
    exact (ageSetoid K r).refl _

def IsoAgeIndex (K : RelStructure L X) := Σ r, IsoAge K r

def isoAgeArity (K : RelStructure L X) (j : IsoAgeIndex K) : ℕ := j.fst

noncomputable def isoAgeFamily (K : RelStructure L X) (j : IsoAgeIndex K) :
    RelStructure L (Fin (isoAgeArity K j)) := (representative K j.fst j.snd).val

theorem finite_iso_age (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hL : L.FinitePerArity) (r : ℕ) : Finite (IsoAge K r) := by
  letI := finite_age_states K hK hL r
  unfold IsoAge
  infer_instance

theorem finite_iso_age_arity (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hL : L.FinitePerArity) (r : ℕ) :
    Finite {j : IsoAgeIndex K // isoAgeArity K j = r} := by
  letI := finite_iso_age K hK hL r
  let f : {j : IsoAgeIndex K // isoAgeArity K j = r} → IsoAge K r := fun j =>
    j.property ▸ j.val.snd
  exact Finite.of_injective f (by
    rintro ⟨⟨s, b⟩, hs⟩ ⟨⟨t, c⟩, ht⟩ h
    change s = r at hs
    change t = r at ht
    subst s
    subst t
    change b = c at h
    cases h
    rfl)

theorem countable_iso_age (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hL : L.FinitePerArity) : Countable (IsoAgeIndex K) := by
  letI : ∀ r, Finite (IsoAge K r) := finite_iso_age K hK hL
  unfold IsoAgeIndex
  infer_instance

theorem isoAgeFamily_realized (K : RelStructure L X) (j : IsoAgeIndex K) :
    Nonempty (RelEmbedding (isoAgeFamily K j) K) := (representative K j.fst j.snd).property

theorem iso_age_family_covers (K : RelStructure L X) :
    ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) →
        ∃ j, ∃ u : RelEmbedding (isoAgeFamily K j) b, Function.Surjective u := by
  classical
  intro F _ b hb
  letI := Fintype.ofFinite F
  let E := Fintype.equivFin F
  let c := b.pullback E.symm
  let u : RelEmbedding c b := RelEmbedding.pullback b E.symm E.symm.injective
  let a : AgeStates K (Fintype.card F) := ⟨c, ⟨(Classical.choice hb).comp u⟩⟩
  let q : IsoAge K (Fintype.card F) := Quotient.mk _ a
  let j : IsoAgeIndex K := ⟨Fintype.card F, q⟩
  have he : ageIso K (Fintype.card F) (representative K _ q) a :=
    Quotient.exact (representative_class K _ q)
  obtain ⟨σ, hσ⟩ := he
  let v : RelEmbedding (isoAgeFamily K j) c := {
    toFun := σ
    injective := σ.injective
    map_rel := fun R t => (congrArg (fun z => z.rel R t) hσ).symm.to_iff }
  exact ⟨j, u.comp v, E.symm.surjective.comp σ.surjective⟩

noncomputable def representativeExpansion (K : RelStructure L X) (Y : RelStructure S X) :=
  expansion (isoAgeFamily K) K Y

theorem representative_finite_per_arity (K : RelStructure L X) (Y : RelStructure S X)
    (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite) :
    (language (isoAgeFamily K) K Y).FinitePerArity := by
  intro r
  letI : Finite (L.Rel r) := hL r
  letI := finite_iso_age_arity K hK hL r
  haveI : Finite (Symbols (isoAgeFamily K) K Y r) :=
    finite_symbols (isoAgeFamily K) K Y
      (fun j => hfin _ (isoAgeFamily K j) (isoAgeFamily_realized K j)) r
  change Finite (L.Rel r ⊕ Symbols (isoAgeFamily K) K Y r)
  infer_instance

noncomputable def representativePaletteEquiv (K : RelStructure L X) (Y : RelStructure S X)
    [IsEmpty (S.Rel 0)] {F : Type} [Finite F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    palette b K Y ≃ palette b K (representativeExpansion K Y) :=
  paletteEquiv (isoAgeFamily K) K Y
    (cover_determines (isoAgeFamily K) K Y (iso_age_family_covers K)) b hb

theorem representativeEmbedding_iff (ι : LanguageInclusion L S)
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hYK : Y.reduct ι = K) (f : X → X) :
    IsEmbeddingMap (representativeExpansion K Y) (representativeExpansion K Y) f ↔
      IsEmbeddingMap Y Y f :=
  embedding_iff_full ι (isoAgeFamily K) K Y hYK
    (cover_determines (isoAgeFamily K) K Y (iso_age_family_covers K)) f

end RelationalRamsey632.Transfer.Named
