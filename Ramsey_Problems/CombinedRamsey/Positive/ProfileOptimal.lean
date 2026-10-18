import CombinedRamsey.Positive.ProfilePrecompactness
import RelationalRamsey632.Transfer.CopyDegrees
import RelationalRamsey632.Transfer.RepresentativeConclusion
import RelationalRamsey632.Source.IntrinsicFin

/-! The whole relational transfer is instantiated with the new original-alphabet marker map. -/

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.RelStructure
open RelationalRamsey632.Coding RelationalRamsey632.Transfer

variable (L : Language) [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)]

theorem return_approximate (K : RelStructure L ℕ)
    (hEP : Existence.OnePointExtensionProperty true K) :
    Approximate K (decoder L) (returnEmbedding L K hEP) := by
  intro F _ b _ u
  let f := (returnEmbedding L K hEP).comp u
  exact ⟨f.injective, fun _ R t => f.map_rel R t⟩

theorem concrete_source_language_positive : (expandedSourceLanguage L).Positive := by
  haveI : IsEmpty ((normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel 0) :=
    normalFormStructure_positive (ProfileAlphabet L) (UnaryProfile L)
  change IsEmpty (L.Rel 0 ⊕ (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel 0)
  infer_instance

omit [IsEmpty (L.Rel 0)] in
theorem concrete_source_language_countable : Countable (Sigma (expandedSourceLanguage L).Rel) := by
  letI := normalFormLanguage_countable (ProfileAlphabet L) (UnaryProfile L)
  haveI : ∀ r, Countable ((expandedSourceLanguage L).Rel r) := fun r => by
    haveI : Countable ((normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r) := by
      haveI := normalFormLanguage_countable (ProfileAlphabet L) (UnaryProfile L)
      exact Function.Embedding.countable
        ⟨Sigma.mk r, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
    change Countable (L.Rel r ⊕ (normalFormLanguage (ProfileAlphabet L) (UnaryProfile L)).Rel r)
    infer_instance
  infer_instance

/-- The complete exact palette/minimum/orbit degree conclusion from the
actual new fixed-alphabet construction, with its Ramsey input proved internally. -/
theorem profile_optimal_expansion (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K)
    :
    ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
      Y.reduct (baseInclusion L) = K ∧
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
            ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩ := by
  haveI := decoderVertex_countable L
  exact countable_big_ramsey_degrees (baseInclusion L) (expandedSource_base L)
    (return_approximate L K hEP) (codingEmbedding L K hK)
    (uniform_source_conditions L K hK)

theorem new_chi_exact_degree (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) {m : ℕ}
    (a : RelStructure L (Fin m)) (ha : Nonempty (RelationalRamsey632.RelEmbedding a K)) :
    ExactEmbeddingDegree a K (Intrinsic.codeMinimumFin (codingMap L K) a K) := by
  exact Intrinsic.exact_codeMinimum_of_source (expandedSource L) (nfInclusion L)
    (expandedSource_nf L) (fun n t ht => expandedSource_normalForm_pullback L t ht)
    (baseInclusion L) (decoder L) (expandedSource_base L) K (returnEmbedding L K hEP)
    (return_approximate L K hEP) (codingEmbedding L K hK) (uniform_source_conditions L K hK) a ha

/-- The minimum uses the literal ordered NF(phi e) from this article's map,
and ranges over every full-language self-embedding of the actual generic. -/
theorem new_chi_exact_minimum (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) {m : ℕ}
    (a : RelStructure L (Fin m)) (ha : Nonempty (RelationalRamsey632.RelEmbedding a K)) :
    ∃ d : ℕ, ExactEmbeddingDegree a K d ∧
      (∀ eta : RelationalRamsey632.RelEmbedding K K,
        d ≤ (Intrinsic.codeRangeFin (codingMap L K ∘ eta) a K).ncard) ∧
      ∃ eta : RelationalRamsey632.RelEmbedding K K,
        (Intrinsic.codeRangeFin (codingMap L K ∘ eta) a K).ncard = d :=
  ⟨Intrinsic.codeMinimumFin (codingMap L K) a K, new_chi_exact_degree L K hK hEP a ha,
    Intrinsic.codeMinimumFin_le (codingMap L K) a K,
    Intrinsic.codeMinimumFin_attained (codingMap L K) a K⟩

omit [IsEmpty (L.Rel 0)] in
theorem profile_normal_forms_bound (K : RelStructure L ℕ) (n : ℕ) :
    (codingNormalForms L K n).Finite ∧ Nat.card (codingNormalForms L K n) ≤
      (Nat.card (UnaryProfile L) * ∑ h : Fin (CombinedRamsey.Positive.originalEnvelopeBound n),
        ∏ r ∈ Finset.Icc 1 h.val, (profileSize L r + 1) ^ h.val.choose r) ^ n := by
  have h := Marker.uniform_normalFormImage_bound (profileColours L) (relationCodes L K)
    (unaryAt L K) n
  change (codingNormalForms L K n).Finite ∧ Nat.card (codingNormalForms L K n) ≤
    (Nat.card (UnaryProfile L) * ∑ h : Fin (CombinedRamsey.Positive.originalEnvelopeBound n),
      ∏ r ∈ Finset.Icc 1 h.val, (profileColours L r + 2) ^ h.val.choose r) ^ n at h
  simpa only [profileColours_add_two] using h

end CombinedRamsey.Positive.Relational

