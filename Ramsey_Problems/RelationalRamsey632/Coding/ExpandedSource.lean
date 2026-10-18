import RelationalRamsey632.Coding.DecoderNormalForm

namespace RelationalRamsey632.Coding

open Source RelStructure

variable (L : Language) [∀ r, Fintype (L.Rel r)]

def expandedSourceLanguage : Language where
  Rel r := L.Rel r ⊕ (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r

def baseInclusion : LanguageInclusion L (expandedSourceLanguage L) where
  relMap _ := Sum.inl
  relInjective _ := Sum.inl_injective

def nfInclusion : LanguageInclusion
    (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)) (expandedSourceLanguage L) where
  relMap _ := Sum.inr
  relInjective _ := Sum.inr_injective

noncomputable def expandedSource : RelStructure (expandedSourceLanguage L) (DecoderVertex L) where
  rel R t := match R with
    | Sum.inl R => (decoder L).rel R t
    | Sum.inr R => (normalFormStructure (ProfileAlphabet L) (UnaryProfile L)).rel R t

@[simp] theorem expandedSource_base : (expandedSource L).reduct (baseInclusion L) = decoder L := rfl

@[simp] theorem expandedSource_nf : (expandedSource L).reduct (nfInclusion L) =
    normalFormStructure (ProfileAlphabet L) (UnaryProfile L) := rfl

def nfReductEmbedding {F : Type} {p : RelStructure (expandedSourceLanguage L) F}
    (e : RelEmbedding p (expandedSource L)) :
    RelEmbedding (p.reduct (nfInclusion L))
      (normalFormStructure (ProfileAlphabet L) (UnaryProfile L)) where
  toFun := e
  injective := e.injective
  map_rel R t := e.map_rel (Sum.inr R) t

def liftFiniteEmbedding {F : Type} (p : RelStructure (expandedSourceLanguage L) F)
    (e : RelEmbedding p (expandedSource L))
    (f : RelEmbedding (p.reduct (nfInclusion L))
      (normalFormStructure (ProfileAlphabet L) (UnaryProfile L))) :
    RelEmbedding p (expandedSource L) where
  toFun := f
  injective := f.injective
  map_rel {r} R t := by
    cases R with
    | inr R => exact f.map_rel R t
    | inl R =>
      apply (e.map_rel (Sum.inl R) t).trans
      change (decoder L).rel R (e ∘ t) ↔ (decoder L).rel R (f ∘ t)
      cases r with
      | zero => rfl
      | succ r =>
        by_cases ht : Function.Injective t
        · exact decoder_normalForm_determined L R (e ∘ t) (f ∘ t)
            (normalForm_of_finiteEmbedding (ProfileAlphabet L) (UnaryProfile L)
              (p.reduct (nfInclusion L)) (nfReductEmbedding L e) f
              (Nat.zero_lt_succ r) t ht)
        · apply iff_of_false
          · intro h
            exact ht (Function.Injective.of_comp
              (decoder_injective L (r + 1) R (e ∘ t) (Nat.zero_lt_succ r) h))
          · intro h
            exact ht (Function.Injective.of_comp
              (decoder_injective L (r + 1) R (f ∘ t) (Nat.zero_lt_succ r) h))

noncomputable def liftSelfEmbedding
    (f : RelEmbedding (normalFormStructure (ProfileAlphabet L) (UnaryProfile L))
      (normalFormStructure (ProfileAlphabet L) (UnaryProfile L))) :
    RelEmbedding (expandedSource L) (expandedSource L) :=
  liftFiniteEmbedding L (expandedSource L) (RelEmbedding.refl _) f

theorem source_degree_one_lift {F : Type}
    (p : RelStructure (expandedSourceLanguage L) F)
    (e : RelEmbedding p (expandedSource L))
    (hR : Transfer.SourceDegreeOne
      (normalFormStructure (ProfileAlphabet L) (UnaryProfile L)) (p.reduct (nfInclusion L))) :
    Transfer.SourceDegreeOne (expandedSource L) p := by
  intro D _ c
  obtain ⟨ζ, hζ⟩ := hR D (fun f => c (liftFiniteEmbedding L p e f))
  refine ⟨liftSelfEmbedding L ζ, ?_⟩
  intro u v
  have hu : liftFiniteEmbedding L p e (ζ.comp (nfReductEmbedding L u)) =
      (liftSelfEmbedding L ζ).comp u := by
    apply RelEmbedding.ext
    intro x
    rfl
  have hv : liftFiniteEmbedding L p e (ζ.comp (nfReductEmbedding L v)) =
      (liftSelfEmbedding L ζ).comp v := by
    apply RelEmbedding.ext
    intro x
    rfl
  rw [← hu, ← hv]
  exact hζ (nfReductEmbedding L u) (nfReductEmbedding L v)

theorem expandedSource_rigid {F : Type} [Finite F]
    (p : RelStructure (expandedSourceLanguage L) F)
    (e : RelEmbedding p (expandedSource L)) : Transfer.Rigid p := by
  intro σ hσ
  have hn : (p.reduct (nfInclusion L)).pullback σ = p.reduct (nfInclusion L) :=
    congrArg (fun z => z.reduct (nfInclusion L)) hσ
  exact normalForm_finite_rigid (ProfileAlphabet L) (UnaryProfile L)
    (p.reduct (nfInclusion L)) ⟨nfReductEmbedding L e⟩ σ hn

theorem expandedSource_normalForm_pullback {n : ℕ}
    (t : Fin n → DecoderVertex L) (ht : Function.Injective t) :
    (expandedSource L).pullback (normalForm t) = (expandedSource L).pullback t := by
  apply RelStructure.ext_rel
  intro r R q
  cases R with
  | inl R =>
    exact decoder_normalForm_determined L R (normalForm t ∘ q) (t ∘ q)
      (normalForm_subtuple t q)
  | inr R =>
    change (Function.Injective (normalForm t ∘ q) ∧ normalForm (normalForm t ∘ q) = R.val) ↔
      (Function.Injective (t ∘ q) ∧ normalForm (t ∘ q) = R.val)
    rw [(normalForm_injective t ht).of_comp_iff q, ht.of_comp_iff q, normalForm_subtuple]

end RelationalRamsey632.Coding
