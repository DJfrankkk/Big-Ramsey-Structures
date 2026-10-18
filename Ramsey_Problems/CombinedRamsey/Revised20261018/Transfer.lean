import CombinedRamsey.Revised20261018.Recoding
import RelationalRamsey632.Transfer.EmptyAndRelabelling

/-! The revised paper's general transfer theorem, including literal
injective naming in a countable language.  The original relations may have
repetitions, unbounded arities, arbitrary symbol sets and nullaries. -/

namespace CombinedRamsey.Revised20261018

open RelationalRamsey632 RelationalRamsey632.RelStructure
open RelationalRamsey632.Transfer RelationalRamsey632.Transfer.Named

variable {L S : Language} {X M : Type}

/-- A one-color upper bound is the literal homogenization property used
by the source machinery; no age or language hypotheses are needed. -/
theorem sourceDegreeOne_of_bound_one {F : Type}
    (p : RelStructure S F) (N : RelStructure S M)
    (h : EmbeddingDegreeBound p N 1) : SourceDegreeOne N p := by
  intro D _ c
  obtain ⟨z, s, hs, hc⟩ := h D c
  exact ⟨z, fun u v => (Finset.card_le_one.mp hs) _ (hc u) _ (hc v)⟩

theorem sourceDegreeOne_iff_exact_degree_one {F : Type}
    (p : RelStructure S F) (N : RelStructure S M)
    (hp : Nonempty (RelEmbedding p N)) :
    SourceDegreeOne N p ↔ ExactEmbeddingDegree p N 1 := by
  constructor
  · exact exact_degree_one_of_source p N hp
  · exact fun h => sourceDegreeOne_of_bound_one p N h.1

def BigRamseyExpansion {T : Language} (ι : LanguageInclusion L T)
    (K : RelStructure L X) (Y : RelStructure T X) : Prop :=
  Y.reduct ι = K ∧
    ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (_hb : Nonempty (RelEmbedding b K)),
      (palette b K Y).Finite ∧ Unavoidable b K Y ∧
        ExactEmbeddingDegree b K (palette b K Y).ncard

theorem embedding_approximate {K : RelStructure L X} {B : RelStructure L M}
    (θ : RelEmbedding B K) : Approximate K B θ := by
  intro F _ a _ u
  exact ⟨(θ.comp u).injective, fun _ R t => (θ.comp u).map_rel R t⟩

/-- The age-X formulation of the manuscript gives exactly the old
precompact source premise; it concerns full expanded types, not reducts. -/
theorem precompact_source_of_age
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (φ : RelEmbedding K B)
    (hpre : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K (N.pullback φ)).Finite)
    (hR : ∀ (F : Type) [Finite F] (p : RelStructure S F),
      Nonempty (RelEmbedding p (N.pullback φ)) → SourceDegreeOne N p) :
    PrecompactSource N φ := by
  intro F _ b hb
  refine ⟨hpre F b hb, ?_⟩
  intro p hp
  obtain ⟨e, he⟩ := hp
  change (N.pullback φ).pullback e = p at he
  apply hR F p
  have u := RelEmbedding.pullback (N.pullback φ) e e.injective
  rw [he] at u
  exact ⟨u⟩

/-- The full-language compatible expansion and the exact minimum formula.
There is no homogeneity or finite-per-arity hypothesis. -/
theorem full_precompact_transfer
    (ι : LanguageInclusion L S) [Countable X] [Countable M]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) (φ : RelEmbedding K B) (θ : RelEmbedding B K)
    (hsource : PrecompactSource N φ) :
    ∃ Y : RelStructure S X, BigRamseyExpansion ι K Y ∧
      ∀ (F : Type) [Finite F] (a : RelStructure L F)
        (_ha : Nonempty (RelEmbedding a K)),
        (∀ η : RelEmbedding K K,
          (palette a K Y).ncard ≤ (palette a K (N.pullback (φ.comp η))).ncard) ∧
        ∃ η : RelEmbedding K K,
          (palette a K Y).ncard = (palette a K (N.pullback (φ.comp η))).ncard := by
  obtain ⟨Y, hY, hall⟩ := countable_big_ramsey_expansion ι hN
    (embedding_approximate θ) φ hsource
  refine ⟨Y, ⟨hY, ?_⟩, ?_⟩
  · intro F _ a ha
    obtain ⟨hf, hu, he, _⟩ := hall F a ha
    exact ⟨hf, hu, he⟩
  · intro F _ a ha
    obtain ⟨_, _, _, hlo, hatt, _⟩ := hall F a ha
    exact ⟨hlo, hatt⟩

/-- Theorem `thm:transfer`: an actual compatible BRS with countably many
added injective symbols; if the base age has finitely many isomorphism
types of each size, the same expansion has finitely many added symbols
of each arity.  Original symbols are retained without restrictions. -/
theorem precompact_transfer
    (ι : LanguageInclusion L S) [Countable X] [Countable M]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) (φ : RelEmbedding K B) (θ : RelEmbedding B K)
    (hpre : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K (N.pullback φ)).Finite)
    (hR : ∀ (F : Type) [Finite F] (p : RelStructure S F),
      Nonempty (RelEmbedding p (N.pullback φ)) → SourceDegreeOne N p) :
    ∃ Y : RelStructure S X,
      BigRamseyExpansion (inclusion (ageFamily K) K Y) K (allAgeExpansion K Y) ∧
      Countable (Σ r, Symbols (ageFamily K) K Y r) ∧
      (∀ r (R : Symbols (ageFamily K) K Y r) (t : Fin r → X),
        (allAgeExpansion K Y).rel (Sum.inr R) t → Function.Injective t) ∧
      ((∀ r, Finite (IsoAge K r)) →
        ∀ r, Finite (Symbols (ageFamily K) K Y r)) ∧
      ∀ (F : Type) [Finite F] (a : RelStructure L F)
        (_ha : Nonempty (RelEmbedding a K)),
        (∀ η : RelEmbedding K K,
          (palette a K (allAgeExpansion K Y)).ncard ≤
            (palette a K (N.pullback (φ.comp η))).ncard) ∧
        ∃ η : RelEmbedding K K,
          (palette a K (allAgeExpansion K Y)).ncard =
            (palette a K (N.pullback (φ.comp η))).ncard := by
  have hsource := precompact_source_of_age φ hpre hR
  obtain ⟨Y, hY, hmin⟩ := full_precompact_transfer ι hN φ θ hsource
  have hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite :=
    fun F _ b hb => (hY.2 F b hb).1
  refine ⟨Y, ⟨rfl, ?_⟩, countable_added_symbols K Y hfin,
    fun _ R t h => added_relations_injective K Y R t h,
    fun hiso => finite_added_symbols K Y hiso hfin, ?_⟩
  · intro F _ a ha
    obtain ⟨hf, hu, he⟩ := hY.2 F a ha
    exact ⟨names_finite_palette (ageFamily K) K Y a hf,
      names_unavoidable (ageFamily K) K Y a hu,
      (allAge_palette_card_arbitrary K Y a ha).symm ▸ he⟩
  · intro F _ a ha
    rw [allAge_palette_card_arbitrary K Y a ha]
    exact hmin F a ha

/-- The same terminal theorem with the manuscript's exact-degree-one
hypothesis verbatim, rather than its proved homogenization equivalent. -/
theorem precompact_transfer_exact_degree_one
    (ι : LanguageInclusion L S) [Countable X] [Countable M]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) (φ : RelEmbedding K B) (θ : RelEmbedding B K)
    (hpre : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K (N.pullback φ)).Finite)
    (hR : ∀ (F : Type) [Finite F] (p : RelStructure S F),
      Nonempty (RelEmbedding p (N.pullback φ)) → ExactEmbeddingDegree p N 1) :
    ∃ Y : RelStructure S X,
      BigRamseyExpansion (inclusion (ageFamily K) K Y) K (allAgeExpansion K Y) ∧
      Countable (Σ r, Symbols (ageFamily K) K Y r) ∧
      (∀ r (R : Symbols (ageFamily K) K Y r) (t : Fin r → X),
        (allAgeExpansion K Y).rel (Sum.inr R) t → Function.Injective t) ∧
      ((∀ r, Finite (IsoAge K r)) →
        ∀ r, Finite (Symbols (ageFamily K) K Y r)) ∧
      ∀ (F : Type) [Finite F] (a : RelStructure L F)
        (_ha : Nonempty (RelEmbedding a K)),
        (∀ η : RelEmbedding K K,
          (palette a K (allAgeExpansion K Y)).ncard ≤
            (palette a K (N.pullback (φ.comp η))).ncard) ∧
        ∃ η : RelEmbedding K K,
          (palette a K (allAgeExpansion K Y)).ncard =
            (palette a K (N.pullback (φ.comp η))).ncard := by
  apply precompact_transfer ι hN φ θ hpre
  intro F _ p hp
  exact sourceDegreeOne_of_bound_one p N (hR F p hp).1

end CombinedRamsey.Revised20261018
