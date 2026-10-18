import CombinedRamsey.Positive.ProfileOptimal
import RelationalRamsey632.Transfer.SizeStabilization

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding
open RelationalRamsey632.Transfer RelationalRamsey632.RelStructure

variable (L : Language) [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)]

def OriginalConclusion (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (Y : RelStructure (expandedSourceLanguage L) ℕ) : Prop :=
  ∀ (F : Type) [Finite F] (b : RelStructure L F)
    (_hb : Nonempty (RelationalRamsey632.RelEmbedding b K)),
    (palette b K Y).Finite ∧ Unavoidable b K Y ∧
    ExactEmbeddingDegree b K (palette b K Y).ncard ∧
    ExactCopyDegree b K
      (Nat.card (MulAction.orbitRel.Quotient (automorphismGroup b) (palette b K Y))) ∧
    (Nat.card (MulAction.orbitRel.Quotient (automorphismGroup b) (palette b K Y))
      = (palette b K Y).ncard / Nat.card (automorphismGroup b)) ∧
    (∀ η : RelationalRamsey632.RelEmbedding K K,
      (palette b K Y).ncard ≤
        (palette b K ((expandedSource L).pullback ((codingEmbedding L K hK).comp η))).ncard) ∧
    (∃ η : RelationalRamsey632.RelEmbedding K K,
      (palette b K Y).ncard =
        (palette b K ((expandedSource L).pullback ((codingEmbedding L K hK).comp η))).ncard) ∧
    (∀ p ∈ palette b K Y, Rigid p) ∧
    ∀ (D : Type) [Fintype D] (c : RelationalRamsey632.RelEmbedding b K → D),
      ∃ g : RelationalRamsey632.RelEmbedding K K, ∃ d : palette b K Y → D,
        ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩

def NamedConclusion (K : RelStructure L ℕ)
    (Y : RelStructure (expandedSourceLanguage L) ℕ) : Prop :=
  (Named.representativeExpansion K Y).reduct (Named.inclusion (Named.isoAgeFamily K) K Y) = K ∧
    (Named.language (Named.isoAgeFamily K) K Y).FinitePerArity ∧
    Countable (Sigma (Named.language (Named.isoAgeFamily K) K Y).Rel) ∧
    (∀ f : ℕ → ℕ,
      IsEmbeddingMap (Named.representativeExpansion K Y) (Named.representativeExpansion K Y) f ↔
        IsEmbeddingMap Y Y f) ∧
    ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (_hb : Nonempty (RelationalRamsey632.RelEmbedding b K)),
      (palette b K (Named.representativeExpansion K Y)).Finite ∧
      Unavoidable b K (Named.representativeExpansion K Y) ∧
      ExactEmbeddingDegree b K (palette b K (Named.representativeExpansion K Y)).ncard ∧
      ExactCopyDegree b K ((palette b K (Named.representativeExpansion K Y)).ncard /
        Nat.card (automorphismGroup b)) ∧
      (palette b K (Named.representativeExpansion K Y)).ncard = (palette b K Y).ncard ∧
      (∀ p ∈ palette b K (Named.representativeExpansion K Y), Rigid p) ∧
      ∀ (D : Type) [Fintype D] (c : RelationalRamsey632.RelEmbedding b K → D),
        ∃ g : RelationalRamsey632.RelEmbedding K K, ∃ d : palette b K (Named.representativeExpansion K Y) → D,
          ∀ e, c (g.comp e) = d ⟨(Named.representativeExpansion K Y).pullback e, ⟨e, rfl⟩⟩

theorem size_indexed_optimal_system (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) :
    ∃ η : ℕ → RelationalRamsey632.RelEmbedding K K, ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
      Y.reduct (baseInclusion L) = K ∧ η 0 = RelationalRamsey632.RelEmbedding.refl K ∧
      (∀ n, ∃ u : RelationalRamsey632.RelEmbedding K K, η (n + 1) = (η n).comp u) ∧
      (∀ m (b : RelStructure L (Fin m)) (_hb : Nonempty (RelationalRamsey632.RelEmbedding b K)),
        ∀ n, m ≤ n → ∀ e : RelationalRamsey632.RelEmbedding b K,
          Y.pullback e =
            ((expandedSource L).pullback ((codingEmbedding L K hK).comp (η n))).pullback e) ∧
      OriginalConclusion L K hK Y ∧ NamedConclusion L K Y := by
  classical
  haveI : IsEmpty ((expandedSourceLanguage L).Rel 0) := concrete_source_language_positive L
  haveI := decoderVertex_countable L
  have hL : L.FinitePerArity := fun _ => inferInstance
  let φ := codingEmbedding L K hK
  let N := expandedSource L
  have hsource : PrecompactSource N φ := uniform_source_conditions L K hK
  have hψ := return_approximate L K hEP
  obtain ⟨η, Y, hY, hzero, hnested, hs, hu⟩ :=
    size_stabilized_expansion (baseInclusion L) hK hL (expandedSource_base L) hψ φ hsource
  have hall : OriginalConclusion L K hK Y := by
    intro F _ b hb
    letI := Fintype.ofFinite F
    let E := Fintype.equivFin F
    let bE := b.pullback E.symm
    let u : RelationalRamsey632.RelEmbedding bE b := RelationalRamsey632.RelEmbedding.pullback b E.symm E.symm.injective
    have hbE : Nonempty (RelationalRamsey632.RelEmbedding bE K) := ⟨(Classical.choice hb).comp u⟩
    let n := Fintype.card F
    let i := φ.comp (η n)
    have ht : ∀ e : RelationalRamsey632.RelEmbedding b K, Y.pullback e = (N.pullback i).pullback e :=
      full_types_transfer u E.symm.surjective Y (N.pullback i) (hs n bE hbE n le_rfl)
    obtain ⟨hfin, hR⟩ := precompact_source_pullback hsource (η n) F b hb
    obtain ⟨hYfin, he, hc⟩ := exact_degree_from_source_stage (baseInclusion L)
      (expandedSource_base L) hψ i hb hfin hR Y ht (hu F b hb)
    have hp : palette b K Y = palette b K (N.pullback i) := congrArg Set.range (funext ht)
    have hr : ∀ p ∈ palette b K Y, Rigid p :=
      fun p hpy => source_palette_rigid i hR p (hp ▸ hpy)
    obtain ⟨hcopy, hdiv⟩ := exact_copy_degree Y hYfin (hu F b hb) hr hc
    refine ⟨hYfin, hu F b hb, he, hcopy, hdiv, ?_, ⟨η n, congrArg Set.ncard hp⟩, hr, hc⟩
    intro α
    obtain ⟨hαfin, hαR⟩ := precompact_source_pullback hsource α F b hb
    exact he.2 _ (source_degree_bound (baseInclusion L) (expandedSource_base L) hψ
      (φ.comp α) hb hαfin hαR)
  refine ⟨η, Y, hY, hzero, hnested, hs, hall, ?_⟩
  exact Named.representative_big_ramsey (baseInclusion L) K Y hY hK hL (by
    intro F _ b hb
    obtain ⟨hf, hU, he, _, _, _, _, hr, hc⟩ := hall F b hb
    exact ⟨hf, hU, he, hr, hc⟩)


end CombinedRamsey.Positive.Relational

