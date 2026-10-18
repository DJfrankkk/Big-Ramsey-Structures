import RelationalRamsey632.Transfer.NamedExpansion
import RelationalRamsey632.Existence.FiniteTypes
import Mathlib.Data.Finite.Sum

/-! A concrete family containing every finite age type.  We use all finite
labelled base structures; there are only finitely many at each size in the
language range of the main theorem.  This harmless redundancy gives an
actual countable positive-arity naming language without a selection oracle. -/

namespace RelationalRamsey632.Transfer.Named

open RelStructure

variable {L S : Language} {X : Type}

def AgeStates (K : RelStructure L X) (r : ℕ) :=
  {b : RelStructure L (Fin r) // Nonempty (RelEmbedding b K)}

def AgeIndex (K : RelStructure L X) := Σ r, AgeStates K r

def ageArity (K : RelStructure L X) (j : AgeIndex K) : ℕ := j.fst

def ageFamily (K : RelStructure L X) (j : AgeIndex K) :
    RelStructure L (Fin (ageArity K j)) := j.snd.val

theorem finite_age_states (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hL : L.FinitePerArity) (r : ℕ) : Finite (AgeStates K r) := by
  classical
  let f : AgeStates K r → Existence.InjectiveStructure L (Fin r) := fun b =>
    ⟨b.val, by
      let e := Classical.choice b.property
      rw [← e.pullback_eq]
      exact RelStructure.injectiveRelations_pullback hK e⟩
  letI := Existence.finite_injective_structures L hL r
  exact Finite.of_injective f (by
    intro b c h
    apply Subtype.ext
    exact congrArg (fun z : Existence.InjectiveStructure L (Fin r) => z.val) h)

theorem countable_age_index (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hL : L.FinitePerArity) : Countable (AgeIndex K) := by
  letI : ∀ r, Finite (AgeStates K r) := finite_age_states K hK hL
  unfold AgeIndex
  infer_instance

theorem finite_age_arity (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hL : L.FinitePerArity) (r : ℕ) :
    Finite {j : AgeIndex K // ageArity K j = r} := by
  classical
  letI := finite_age_states K hK hL r
  let f : {j : AgeIndex K // ageArity K j = r} → AgeStates K r := fun j =>
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

theorem age_family_covers (K : RelStructure L X) :
    ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) →
        ∃ j, ∃ u : RelEmbedding (ageFamily K j) b, Function.Surjective u := by
  classical
  intro F _ b hb
  letI : Fintype F := Fintype.ofFinite F
  let E := Fintype.equivFin F
  let c := b.pullback E.symm
  let u : RelEmbedding c b := RelEmbedding.pullback b E.symm E.symm.injective
  let j : AgeIndex K := ⟨Fintype.card F, c, ⟨(Classical.choice hb).comp u⟩⟩
  exact ⟨j, u, E.symm.surjective⟩

abbrev allAgeExpansion (K : RelStructure L X) (Y : RelStructure S X) :=
  expansion (ageFamily K) K Y

theorem allAgeFinitePerArity (K : RelStructure L X) (Y : RelStructure S X)
    (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite) :
    (language (ageFamily K) K Y).FinitePerArity := by
  intro r
  haveI : Finite (L.Rel r) := hL r
  haveI : Finite {j : AgeIndex K // ageArity K j = r} := finite_age_arity K hK hL r
  haveI : Finite (Symbols (ageFamily K) K Y r) := finite_symbols (ageFamily K) K Y
    (fun j => hfin _ (ageFamily K j) j.snd.property) r
  change Finite (L.Rel r ⊕ Symbols (ageFamily K) K Y r)
  infer_instance

theorem allAge_positive (K : RelStructure L X) (Y : RelStructure S X)
    [IsEmpty (L.Rel 0)] : (language (ageFamily K) K Y).Positive := by
  letI := no_nullary_names (ageFamily K) K Y
  change IsEmpty (L.Rel 0 ⊕ Symbols (ageFamily K) K Y 0)
  infer_instance

theorem allAgeEmbedding_iff (ι : LanguageInclusion L S)
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hYK : Y.reduct ι = K) (f : X → X) :
    IsEmbeddingMap (allAgeExpansion K Y) (allAgeExpansion K Y) f ↔
      IsEmbeddingMap Y Y f :=
  embedding_iff_full ι (ageFamily K) K Y hYK
    (cover_determines (ageFamily K) K Y (age_family_covers K)) f

noncomputable def allAgePaletteEquiv (K : RelStructure L X) (Y : RelStructure S X)
    [IsEmpty (S.Rel 0)] {F : Type} [Finite F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    palette b K Y ≃ palette b K (allAgeExpansion K Y) :=
  paletteEquiv (ageFamily K) K Y
    (cover_determines (ageFamily K) K Y (age_family_covers K)) b hb

theorem allAgeInjectiveRelations (K : RelStructure L X) (Y : RelStructure S X)
    (hK : K.InjectiveRelations) : (allAgeExpansion K Y).InjectiveRelations := by
  intro r R t hr ht
  cases R with
  | inl R => exact hK r R t hr ht
  | inr R =>
    rcases R with ⟨j, q⟩
    have hi : Function.Injective (t ∘ Fin.cast j.property.1) := ht.1
    intro x y hxy
    have he := hi (show t (Fin.cast j.property.1 (Fin.cast j.property.1.symm x)) =
        t (Fin.cast j.property.1 (Fin.cast j.property.1.symm y)) by simpa using hxy)
    exact (Fin.cast_injective j.property.1.symm) he

theorem allAgeCountableSymbols (K : RelStructure L X) (Y : RelStructure S X)
    (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite) :
    Countable (Sigma (language (ageFamily K) K Y).Rel) := by
  have hC := allAgeFinitePerArity K Y hK hL hfin
  letI : ∀ r, Finite ((language (ageFamily K) K Y).Rel r) := hC
  infer_instance

/-- All structural big Ramsey conclusions pass to the actual naming
language. The same finite labelled palettes are identified by an explicit
bijection, including pullback covariance and the empty structure. -/
theorem allAgeBigRamsey (ι : LanguageInclusion L S)
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
    (allAgeExpansion K Y).reduct (inclusion (ageFamily K) K Y) = K ∧
    (language (ageFamily K) K Y).FinitePerArity ∧
    Countable (Sigma (language (ageFamily K) K Y).Rel) ∧
    (allAgeExpansion K Y).InjectiveRelations ∧
    (∀ f : X → X, IsEmbeddingMap (allAgeExpansion K Y) (allAgeExpansion K Y) f ↔
      IsEmbeddingMap Y Y f) ∧
    ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (_hb : Nonempty (RelEmbedding b K)),
      (palette b K (allAgeExpansion K Y)).Finite ∧
      Unavoidable b K (allAgeExpansion K Y) ∧
      ExactEmbeddingDegree b K (palette b K (allAgeExpansion K Y)).ncard ∧
      ExactCopyDegree b K ((palette b K (allAgeExpansion K Y)).ncard /
        Nat.card (automorphismGroup b)) ∧
      (∀ p ∈ palette b K (allAgeExpansion K Y), Rigid p) ∧
      ∀ (D : Type) [Fintype D] (c : RelEmbedding b K → D),
        ∃ g : RelEmbedding K K, ∃ d : palette b K (allAgeExpansion K Y) → D,
          ∀ e, c (g.comp e) = d ⟨(allAgeExpansion K Y).pullback e, ⟨e, rfl⟩⟩ := by
  have hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite :=
    fun F _ b hb => (hall F b hb).1
  have hD := cover_determines (ageFamily K) K Y (age_family_covers K)
  refine ⟨rfl, allAgeFinitePerArity K Y hK hL hfin,
    allAgeCountableSymbols K Y hK hL hfin, allAgeInjectiveRelations K Y hK,
    allAgeEmbedding_iff ι K Y hYK, ?_⟩
  intro F _ b hb
  obtain ⟨hf, hu, he, hr, hc⟩ := hall F b hb
  have hfC := names_finite_palette (ageFamily K) K Y b hf
  have huC := names_unavoidable (ageFamily K) K Y b hu
  have hrC := names_rigid (ageFamily K) K Y hD b hb hr
  have hcC := names_canonization (ageFamily K) K Y hD b hb hc
  have hcard := names_palette_card (ageFamily K) K Y hD b hb
  obtain ⟨hcopy, hdiv⟩ := exact_copy_degree (allAgeExpansion K Y) hfC huC hrC hcC
  refine ⟨hfC, huC, hcard ▸ he, ?_, hrC, hcC⟩
  exact hdiv ▸ hcopy

theorem named_big_ramsey_from_source {M : Type}
    (ι : LanguageInclusion L S) [Countable X] [Countable M] [IsEmpty (S.Rel 0)]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ) :
    ∃ Y : RelStructure S X, Y.reduct ι = K ∧
      (language (ageFamily K) K Y).FinitePerArity ∧
      Countable (Sigma (language (ageFamily K) K Y).Rel) ∧
      ∀ (F : Type) [Finite F] (b : RelStructure L F)
        (_hb : Nonempty (RelEmbedding b K)),
        ExactEmbeddingDegree b K (palette b K (allAgeExpansion K Y)).ncard ∧
        ExactCopyDegree b K ((palette b K (allAgeExpansion K Y)).ncard /
          Nat.card (automorphismGroup b)) := by
  obtain ⟨Y, hY, hall⟩ := countable_big_ramsey_expansion ι hN hψ φ hsource
  have hn := allAgeBigRamsey ι K Y hY hK hL (by
    intro F _ b hb
    obtain ⟨hf, hu, he, _, _, hr, hc⟩ := hall F b hb
    exact ⟨hf, hu, he, hr, hc⟩)
  refine ⟨Y, hY, hn.2.1, hn.2.2.1, ?_⟩
  intro F _ b hb
  exact ⟨(hn.2.2.2.2.2 F b hb).2.2.1, (hn.2.2.2.2.2 F b hb).2.2.2.1⟩

end RelationalRamsey632.Transfer.Named
